import Certificates.JsonDecode
import Certificates.JsonDecodeTests
import Certificates.LCChecker
import Certificates.Graphs
import Certificates.RawClosedGraph
import Certificates.RawClosedGraphTests
import Certificates.ValidatedClosedGraph
import Certificates.TypedClosedGraph

def main : IO Unit := do
  readCertificate "../cubic-jordan/projects/f4/certificates/t10/sources_0000.json"
