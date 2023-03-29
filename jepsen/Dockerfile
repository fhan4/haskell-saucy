FROM golang:1.7.4

RUN apt-get --allow-unauthenticated update && apt-get install -y --allow-unauthenticated --no-install-recommends zip openssh-server \
	&& rm -rf /var/lib/apt/lists/*
RUN apt-get install --reinstall ca-certificates

RUN update-ca-certificates && git config --global http.sslCAinfo /etc/ssl/certs/ca-certificates.crt \
	&& git config --global http.sslverify false

ENV CGO_ENABLED 1

RUN mkdir /root/.ssh && chmod 700 /root/.ssh
ADD ./secret/authorized_keys /root/.ssh/authorized_keys
RUN chmod 600 /root/.ssh/authorized_keys && \
	sed -i "s/#PermitRootLogin prohibit-password/PermitRootLogin yes/g" /etc/ssh/sshd_config
EXPOSE 22

# get abci and merkleeyes repos
RUN curl https://raw.githubusercontent.com/golang/dep/master/install.sh | sh \ 
	&& go get -d github.com/tendermint/abci ; exit 0
#RUN go get -d github.com/tendermint/merkleeyes ; exit 0
RUN mkdir -p $GOPATH/src/github.com/tendermint/merkleeyes

# build abci
#WORKDIR $GOPATH/src/github.com/tendermint/abci
#RUN make get_vendor_deps && make install

# install merkleeyes
ADD merkleeyes $GOPATH/src/github.com/tendermint/merkleeyes
#ADD merkleeyes $GOPATH/src/github.com/tendermint/merkleeyes
#ADD containergitconfig $GOPATH/.gitconfig
#WORKDIR $GOPATH/src/github.com/tendermint/merkleeyes
#RUN ls $GOPATH/src/github.com/
#RUN ls $GOPATH
#RUN ls $GOPATH/src/github.com/
#RUN ls -alt $GOPATH/src/github.com/tendermint/merkleeyes
#RUN make tools && make get_vendor_deps
#RUN gox -os="linux" -arch="amd64" -output "$GOPATH/bin/merkleeyes" github.com/tendermint/merkleeyes/cmd/merkleeyes

# get tenderming binary
# RUN mkdir -p $GOPATH/src/github.com/tendermint/tendermint
RUN curl -L https://github.com/tendermint/tendermint/releases/download/v0.10.2/tendermint_0.10.2_linux_amd64.zip -o /tmp/tendermint_0.10.2_linux_amd64.zip
RUN apt-get --allow-unauthenticated update && apt-get -y --allow-unauthenticated install unzip
RUN unzip /tmp/tendermint_0.10.2_linux_amd64.zip -d /bin/

RUN apt-get --allow-unauthenticated -y install dos2unix

WORKDIR $GOPATH/src/github.com/tendermint/
EXPOSE 46656
EXPOSE 46657

ADD cmd_script.sh /root/cmd_script.sh
#ADD tendermint_start.sh /root/tendermint_start.sh
RUN chmod +x /root/cmd_script.sh

RUN dos2unix /root/cmd_script.sh
#CMD ["/usr/sbin/sshd", "-D"]
#CMD ["$GOPATH/bin/merkleeyes", "start", "--address 'unix:///root/data.sock'", "--dbName jepsen"]
#CMD ["/bin/tendermint", "node", "--proxy_app 'unix:///root/data.sock'", "--home '/root/.tendermint'"]

# add RPC scripts to the containers
ADD ./scripts /root/scripts
RUN chmod +x /root/scripts/*.sh
ENV PATH="$PATH:/root/scripts"

ENTRYPOINT ["/root/cmd_script.sh"]
