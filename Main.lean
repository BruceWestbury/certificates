-- import Certificates.JsonDecode   -- temporarily disabled: old direct decoder needs rework
import Certificates.Graphs
import Certificates.RawClosedGraph
import Certificates.RawClosedGraphTests
import Certificates.ValidatedClosedGraph

def main : IO Unit := do
  pure ()   -- placeholder: readCertificate will be restored once the new pipeline is wired up
