rm(list=ls())
options(echo=TRUE) # if you want see commands in output file
args <- commandArgs(trailingOnly = TRUE)
vp = args[1]

dat = read.table(paste0(vp,"_temp.txt"))
datout = aggregate(dat[,15], by=list(dat[,1],dat[,2],dat[,3],dat[,4],dat[,5],dat[,6],dat[,7],dat[,8],dat[,9],dat[,10],dat[,11]), paste, collapse=", ")
colnames(datout) = c("chrom","start","end","num","list","22Rv1_rep1","22Rv1_rep2","22Rv1_rep3","RWPE1_rep1","RWPE1_rep2","RWPE1_rep3","genes")
write.table(datout,file=paste0(vp,"_genes_temp.txt"),quote=FALSE,row.names=FALSE,col.names=FALSE,sep="\t")
