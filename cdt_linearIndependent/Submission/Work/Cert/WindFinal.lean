import Submission.Work.Cert.WChunks.W000
import Submission.Work.Cert.WChunks.W001
import Submission.Work.Cert.WChunks.W002
import Submission.Work.Cert.WChunks.W003
import Submission.Work.Cert.WChunks.W004
import Submission.Work.Cert.WChunks.W005
import Submission.Work.Cert.WChunks.W006
import Submission.Work.Cert.WChunks.W007
import Submission.Work.Cert.WChunks.W008
import Submission.Work.Cert.WChunks.W009
import Submission.Work.Cert.WChunks.W010
import Submission.Work.Cert.WChunks.W011
import Submission.Work.Cert.WChunks.W012
import Submission.Work.Cert.WChunks.W013
import Submission.Work.Cert.WChunks.W014
import Submission.Work.Cert.WChunks.W015
import Submission.Work.Cert.WChunks.W016
import Submission.Work.Cert.WChunks.W017
import Submission.Work.Cert.WChunks.W018
import Submission.Work.Cert.WChunks.W019
import Submission.Work.Cert.WChunks.W020
import Submission.Work.Cert.WChunks.W021
import Submission.Work.Cert.WChunks.W022
import Submission.Work.Cert.WChunks.W023
import Submission.Work.Cert.WChunks.W024
import Submission.Work.Cert.WChunks.W025
import Submission.Work.Cert.WChunks.W026
import Submission.Work.Cert.WChunks.W027
import Submission.Work.Cert.WChunks.W028
import Submission.Work.Cert.WChunks.W029
import Submission.Work.Cert.WChunks.W030
import Submission.Work.Cert.WChunks.W031
import Submission.Work.Cert.WChunks.W032
import Submission.Work.Cert.WChunks.W033
import Submission.Work.Cert.WChunks.W034
import Submission.Work.Cert.WChunks.W035
import Submission.Work.Cert.WChunks.W036
import Submission.Work.Cert.WChunks.W037
import Submission.Work.Cert.WChunks.W038
import Submission.Work.Cert.WChunks.W039
import Submission.Work.Cert.WChunks.W040
import Submission.Work.Cert.WChunks.W041
import Submission.Work.Cert.WChunks.W042
import Submission.Work.Cert.WChunks.W043
import Submission.Work.Cert.WChunks.W044
import Submission.Work.Cert.WChunks.W045
set_option maxRecDepth 100000
namespace Work.Cert.WFinal
open Work.Cert Work.Cert.WChunks

/-- all winding arcs of the unit circle, `j = 0 … 4095` in order. -/
def warcsAll : List WArc :=
  arcsW000 ++
  arcsW001 ++
  arcsW002 ++
  arcsW003 ++
  arcsW004 ++
  arcsW005 ++
  arcsW006 ++
  arcsW007 ++
  arcsW008 ++
  arcsW009 ++
  arcsW010 ++
  arcsW011 ++
  arcsW012 ++
  arcsW013 ++
  arcsW014 ++
  arcsW015 ++
  arcsW016 ++
  arcsW017 ++
  arcsW018 ++
  arcsW019 ++
  arcsW020 ++
  arcsW021 ++
  arcsW022 ++
  arcsW023 ++
  arcsW024 ++
  arcsW025 ++
  arcsW026 ++
  arcsW027 ++
  arcsW028 ++
  arcsW029 ++
  arcsW030 ++
  arcsW031 ++
  arcsW032 ++
  arcsW033 ++
  arcsW034 ++
  arcsW035 ++
  arcsW036 ++
  arcsW037 ++
  arcsW038 ++
  arcsW039 ++
  arcsW040 ++
  arcsW041 ++
  arcsW042 ++
  arcsW043 ++
  arcsW044 ++
  arcsW045

def wendsAll : List (Int × Int) := [endW000, endW001, endW002, endW003, endW004, endW005, endW006, endW007, endW008, endW009, endW010, endW011, endW012, endW013, endW014, endW015, endW016, endW017, endW018, endW019, endW020, endW021, endW022, endW023, endW024, endW025, endW026, endW027, endW028, endW029, endW030, endW031, endW032, endW033, endW034, endW035, endW036, endW037, endW038, endW039, endW040, endW041, endW042, endW043, endW044, endW045]
def wstartsAll : List (Int × Int) := [(match arcsW000 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW001 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW002 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW003 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW004 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW005 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW006 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW007 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW008 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW009 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW010 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW011 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW012 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW013 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW014 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW015 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW016 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW017 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW018 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW019 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW020 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW021 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW022 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW023 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW024 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW025 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW026 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW027 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW028 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW029 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW030 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW031 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW032 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW033 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW034 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW035 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW036 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW037 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW038 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW039 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW040 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW041 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW042 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW043 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW044 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0)), (match arcsW045 with | a :: _ => (a.Ex, a.Ey) | [] => (0, 0))]

/-- chunk `i` ends where chunk `i+1` starts; the circle starts and ends at `(S, 0)`. -/
def wlinkOK : List (Int × Int) → List (Int × Int) → Bool
  | s :: s' :: rest, e :: es => decide (e = s') && wlinkOK (s' :: rest) es
  | [_], [e] => decide (e = (S, 0))
  | _, _ => false

theorem wlink_ok : wlinkOK wstartsAll wendsAll = true := by decide +kernel
theorem wfirst_ok : wstartsAll.head? = some (S, 0) := by decide +kernel
theorem wj_ok : warcsAll.map (·.j) = List.range 4096 := by decide +kernel
theorem wlabels_ok : labelsOK (warcsAll.map (·.lab)) = true := by decide +kernel

end Work.Cert.WFinal
