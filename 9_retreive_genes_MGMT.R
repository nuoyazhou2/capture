rm(list=ls())
#args = commandArgs(trailingOnly=TRUE)

library("biomaRt")
#ensembl54=useMart("ENSEMBL_MART_ENSEMBL", host="may2009.archive.ensembl.org/biomart/martservice/", dataset="hsapiens_gene_ensembl")
#ensembl54=useMart("ENSEMBL_MART_ENSEMBL", host="may2009.archive.ensembl.org/biomart/martservice/", dataset="mmusculus_gene_ensembl")
#input = args[1]
#extend = 10000

#ensembl67=useMart("ENSEMBL_MART_ENSEMBL", host="may2012.archive.ensembl.org")
#listDatasets(ensembl67)[grep("Mus",listDatasets(ensembl67)$description),]
table = read.table("../overlap/MGMT.bed")

# this is for mouse NCBIM37(mm9)
#ensembl67=useMart("ENSEMBL_MART_ENSEMBL", host="may2012.archive.ensembl.org", dataset="mmusculus_gene_ensembl")
# this is for human GRCh37(hg19)
ensembl67=useMart("ENSEMBL_MART_ENSEMBL", host="may2012.archive.ensembl.org", dataset="hsapiens_gene_ensembl")
#ensembl = useMart("ensembl",dataset="hsapiens_gene_ensembl")
#listAttributes(ensembl67)[grep("gene_name", listAttributes(ensembl67)$name),]
#listFilters(ensembl67)[grep("biotype", listFilters(ensembl67)$name),]


f  = function(x, output) {
	start = as.numeric(x[2])-10000
	end = as.numeric(x[3])+10000
	chr.region = paste(sub("chr", "", x[1]),start,end, sep=":")
	results=getBM(attributes = c("external_gene_id"), 
               filters = c("chromosomal_region"), 
               values = chr.region, 
               mart = ensembl67)	
	gene_ids = unique(results$external_gene_id)
	gene_ids = gene_ids[!is.na(gene_ids)]
	gene_ids_collapse = paste(gene_ids, sep=",", collapse=",")
	cat(paste(x[1], x[2], x[3], x[4], x[5], gene_ids_collapse, sep="\t"), "\n", file= output, append = T)
	
}

apply(table, 1, f, output = "MGMT_genes.txt")

no_col <- max(count.fields("MGMT_genes.txt", sep = "\t"))
dat = read.table("MGMT_genes.txt", fill=TRUE, col.names=1:no_col)

col_vector = as.vector(dat$X5)
col_vector = col_vector[col_vector != ""]
genes = paste(col_vector, collapse=",")
genes = unique(unlist(strsplit(genes, ",")))

cat(genes, file="MGMT_gene_names.txt", sep="\n")
