import Certificates.JsonDecode
import Certificates.StepChecker

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let text ← IO.FS.readFile path
      match decodeCertificate text with
      | Except.error e =>
          IO.eprintln s!"decode failed: {e}"
          return 1
      | Except.ok cert =>
          match StepChecker.checkAllSteps cert with
          | Except.ok _ =>
              IO.println "ok"
              return 0
          | Except.error e =>
              IO.eprintln s!"step check failed: {e}"
              return 1
  | _ =>
      IO.eprintln "usage: lake exe cert_check <path-to-json>"
      return 2
