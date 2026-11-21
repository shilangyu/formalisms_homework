import Lake

open System Lake DSL

package formalisms_solutions where
  version := v!"0.1.0"
  extraDepTargets := #[`typst]

lean_lib FormalismsSolutions

@[default_target] lean_exe formalisms_solutions where root := `Main

target typst : Array FilePath := do
  Job.async do
    let entries ← System.FilePath.readDir "FormalismsSolutions"
    let mut pdfs : Array FilePath := #[]
    for entry in entries do
      if entry.path.extension == some "typ" then
        let outPdf := entry.path.withExtension "pdf"
        let res ← IO.Process.output {
          cmd := "typst"
          args := #["compile", entry.path.toString, outPdf.toString]
        }
        if res.exitCode != 0 then
          error s!"typst failed on {entry.path}:\n{res.stdout}\n{res.stderr}"
        pdfs := pdfs.push outPdf
    return pdfs
