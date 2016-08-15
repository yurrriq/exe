default:
	echo "-define(VERSION,\"`git rev-parse HEAD | head -c 6`\")." > include/exe.hrl
	./mad dep com pla bun exe
