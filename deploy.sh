REMOTE="ubuntu@ursus-tools.dev"
cp ./build/spec/Hipo.html ./build/spec/index.html
ssh $REMOTE "rm -r /home/ubuntu/hipo/build"
ssh $REMOTE "mkdir /home/ubuntu/hipo/build"
scp -r ./build/spec/* $REMOTE:/home/ubuntu/hipo/build