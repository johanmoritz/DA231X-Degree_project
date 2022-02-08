from bisect import bisect_left
import os
import glob

zotero_export_parh = "/mnt/c/Users/johan.moritz/Downloads"
bibliography_file = "bibliography.bib"

project_folder_path = os.path.dirname(os.path.abspath(__file__))

exported_file = glob.glob(zotero_export_parh + "/*.bib")[0]

with open(exported_file, "r") as e_file:
    content = e_file.readlines()

# Remove exported file
os.remove(exported_file)

with open(bibliography_file, "a") as b_file:
    b_file.write("\n")
    b_file.writelines(content)

ref_tmp = next(filter(lambda x: "@" in x, content))
ref = ref_tmp[ref_tmp.index("{")+1:ref_tmp.index(",")]
title = next(filter(lambda x: "\ttitle =" in x, content)).split("{")[1].split("}")[0]

print("Imported " + title + " with ref " + ref)
