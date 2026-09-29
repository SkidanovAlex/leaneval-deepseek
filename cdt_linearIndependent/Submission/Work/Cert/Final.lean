import Submission.Work.Cert.Chunks.C000
import Submission.Work.Cert.Chunks.C001
import Submission.Work.Cert.Chunks.C002
import Submission.Work.Cert.Chunks.C003
import Submission.Work.Cert.Chunks.C004
import Submission.Work.Cert.Chunks.C005
import Submission.Work.Cert.Chunks.C006
import Submission.Work.Cert.Chunks.C007
import Submission.Work.Cert.Chunks.C008
import Submission.Work.Cert.Chunks.C009
import Submission.Work.Cert.Chunks.C010
import Submission.Work.Cert.Chunks.C011
import Submission.Work.Cert.Chunks.C012
import Submission.Work.Cert.Chunks.C013
import Submission.Work.Cert.Chunks.C014
import Submission.Work.Cert.Chunks.C015
import Submission.Work.Cert.Chunks.C016
import Submission.Work.Cert.Chunks.C017
import Submission.Work.Cert.Chunks.C018
import Submission.Work.Cert.Chunks.C019
import Submission.Work.Cert.Chunks.C020
import Submission.Work.Cert.Chunks.C021
import Submission.Work.Cert.Chunks.C022
import Submission.Work.Cert.Chunks.C023
import Submission.Work.Cert.Chunks.C024
import Submission.Work.Cert.Chunks.C025
import Submission.Work.Cert.Chunks.C026
import Submission.Work.Cert.Chunks.C027
import Submission.Work.Cert.Chunks.C028
import Submission.Work.Cert.Chunks.C029
import Submission.Work.Cert.Chunks.C030
import Submission.Work.Cert.Chunks.C031
import Submission.Work.Cert.Chunks.C032
import Submission.Work.Cert.Chunks.C033
import Submission.Work.Cert.Chunks.C034
import Submission.Work.Cert.Chunks.C035
import Submission.Work.Cert.Chunks.C036
import Submission.Work.Cert.Chunks.C037
import Submission.Work.Cert.Chunks.C038
import Submission.Work.Cert.Chunks.C039
import Submission.Work.Cert.Chunks.C040
import Submission.Work.Cert.Chunks.C041
import Submission.Work.Cert.Chunks.C042
import Submission.Work.Cert.Chunks.C043
import Submission.Work.Cert.Chunks.C044
import Submission.Work.Cert.Chunks.C045
import Submission.Work.Cert.Chunks.C046
import Submission.Work.Cert.Chunks.C047
import Submission.Work.Cert.Chunks.C048
import Submission.Work.Cert.Chunks.C049
import Submission.Work.Cert.Chunks.C050
import Submission.Work.Cert.Chunks.C051
import Submission.Work.Cert.Chunks.C052
import Submission.Work.Cert.Chunks.C053
import Submission.Work.Cert.Chunks.C054
import Submission.Work.Cert.Chunks.C055
import Submission.Work.Cert.Chunks.C056
import Submission.Work.Cert.Chunks.C057
import Submission.Work.Cert.Chunks.C058
import Submission.Work.Cert.Chunks.C059
import Submission.Work.Cert.Chunks.C060
import Submission.Work.Cert.Chunks.C061
import Submission.Work.Cert.Chunks.C062
import Submission.Work.Cert.Chunks.C063
import Submission.Work.Cert.Chunks.C064
import Submission.Work.Cert.Chunks.C065
import Submission.Work.Cert.Chunks.C066
import Submission.Work.Cert.Chunks.C067
import Submission.Work.Cert.Chunks.C068
import Submission.Work.Cert.Chunks.C069
import Submission.Work.Cert.Chunks.C070
import Submission.Work.Cert.Chunks.C071
import Submission.Work.Cert.Chunks.C072
import Submission.Work.Cert.Chunks.C073
import Submission.Work.Cert.Chunks.C074
import Submission.Work.Cert.Chunks.C075
import Submission.Work.Cert.Chunks.C076
import Submission.Work.Cert.Chunks.C077
import Submission.Work.Cert.Chunks.C078
import Submission.Work.Cert.Chunks.C079
import Submission.Work.Cert.Chunks.C080
import Submission.Work.Cert.Chunks.C081
import Submission.Work.Cert.Chunks.C082
import Submission.Work.Cert.Chunks.C083
import Submission.Work.Cert.Chunks.C084
import Submission.Work.Cert.Chunks.C085
import Submission.Work.Cert.Chunks.C086
import Submission.Work.Cert.Chunks.C087
import Submission.Work.Cert.Chunks.C088
import Submission.Work.Cert.Chunks.C089
import Submission.Work.Cert.Chunks.C090
import Submission.Work.Cert.Chunks.C091
import Submission.Work.Cert.Chunks.C092
import Submission.Work.Cert.Chunks.C093
import Submission.Work.Cert.Chunks.C094
import Submission.Work.Cert.Chunks.C095
import Submission.Work.Cert.Chunks.C096
set_option maxRecDepth 100000
namespace Work.Cert.Final
open Work.Cert Work.Cert.Chunks

/-- all arcs of the three circles on the 1024-grid (certificate v4), in order: circle 0 (j = 0..1023), 1, 2. -/
def arcsAll : List ArcD :=
  arcsC000 ++
  arcsC001 ++
  arcsC002 ++
  arcsC003 ++
  arcsC004 ++
  arcsC005 ++
  arcsC006 ++
  arcsC007 ++
  arcsC008 ++
  arcsC009 ++
  arcsC010 ++
  arcsC011 ++
  arcsC012 ++
  arcsC013 ++
  arcsC014 ++
  arcsC015 ++
  arcsC016 ++
  arcsC017 ++
  arcsC018 ++
  arcsC019 ++
  arcsC020 ++
  arcsC021 ++
  arcsC022 ++
  arcsC023 ++
  arcsC024 ++
  arcsC025 ++
  arcsC026 ++
  arcsC027 ++
  arcsC028 ++
  arcsC029 ++
  arcsC030 ++
  arcsC031 ++
  arcsC032 ++
  arcsC033 ++
  arcsC034 ++
  arcsC035 ++
  arcsC036 ++
  arcsC037 ++
  arcsC038 ++
  arcsC039 ++
  arcsC040 ++
  arcsC041 ++
  arcsC042 ++
  arcsC043 ++
  arcsC044 ++
  arcsC045 ++
  arcsC046 ++
  arcsC047 ++
  arcsC048 ++
  arcsC049 ++
  arcsC050 ++
  arcsC051 ++
  arcsC052 ++
  arcsC053 ++
  arcsC054 ++
  arcsC055 ++
  arcsC056 ++
  arcsC057 ++
  arcsC058 ++
  arcsC059 ++
  arcsC060 ++
  arcsC061 ++
  arcsC062 ++
  arcsC063 ++
  arcsC064 ++
  arcsC065 ++
  arcsC066 ++
  arcsC067 ++
  arcsC068 ++
  arcsC069 ++
  arcsC070 ++
  arcsC071 ++
  arcsC072 ++
  arcsC073 ++
  arcsC074 ++
  arcsC075 ++
  arcsC076 ++
  arcsC077 ++
  arcsC078 ++
  arcsC079 ++
  arcsC080 ++
  arcsC081 ++
  arcsC082 ++
  arcsC083 ++
  arcsC084 ++
  arcsC085 ++
  arcsC086 ++
  arcsC087 ++
  arcsC088 ++
  arcsC089 ++
  arcsC090 ++
  arcsC091 ++
  arcsC092 ++
  arcsC093 ++
  arcsC094 ++
  arcsC095 ++
  arcsC096

def endsAll : List (Int × Int) := [endC000, endC001, endC002, endC003, endC004, endC005, endC006, endC007, endC008, endC009, endC010, endC011, endC012, endC013, endC014, endC015, endC016, endC017, endC018, endC019, endC020, endC021, endC022, endC023, endC024, endC025, endC026, endC027, endC028, endC029, endC030, endC031, endC032, endC033, endC034, endC035, endC036, endC037, endC038, endC039, endC040, endC041, endC042, endC043, endC044, endC045, endC046, endC047, endC048, endC049, endC050, endC051, endC052, endC053, endC054, endC055, endC056, endC057, endC058, endC059, endC060, endC061, endC062, endC063, endC064, endC065, endC066, endC067, endC068, endC069, endC070, endC071, endC072, endC073, endC074, endC075, endC076, endC077, endC078, endC079, endC080, endC081, endC082, endC083, endC084, endC085, endC086, endC087, endC088, endC089, endC090, endC091, endC092, endC093, endC094, endC095, endC096]

def startsAll : List (Nat × Int × Int) := [(match arcsC000 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC001 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC002 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC003 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC004 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC005 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC006 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC007 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC008 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC009 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC010 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC011 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC012 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC013 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC014 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC015 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC016 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC017 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC018 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC019 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC020 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC021 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC022 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC023 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC024 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC025 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC026 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC027 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC028 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC029 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC030 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC031 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC032 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC033 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC034 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC035 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC036 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC037 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC038 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC039 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC040 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC041 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC042 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC043 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC044 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC045 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC046 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC047 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC048 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC049 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC050 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC051 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC052 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC053 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC054 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC055 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC056 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC057 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC058 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC059 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC060 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC061 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC062 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC063 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC064 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC065 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC066 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC067 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC068 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC069 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC070 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC071 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC072 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC073 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC074 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC075 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC076 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC077 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC078 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC079 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC080 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC081 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC082 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC083 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC084 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC085 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC086 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC087 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC088 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC089 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC090 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC091 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC092 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC093 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC094 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC095 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0)), (match arcsC096 with | a :: _ => (a.k, a.Ex, a.Ey) | [] => (9, 0, 0))]

/-- consecutive chunks of the same circle link up; a circle starts and ends at `(Rk, 0)`. -/
def linkOK : List (Nat × Int × Int) → List (Int × Int) → Bool
  | (k, ex, ey) :: (k', ex', ey') :: rest, e :: es =>
      (if k = k' then decide (e.1 = ex') && decide (e.2 = ey')
       else decide (e.1 = Rk k) && decide (e.2 = 0) && decide (ex' = Rk k') && decide (ey' = 0)) &&
      linkOK ((k', ex', ey') :: rest) es
  | [(k, _, _)], [e] => decide (e.1 = Rk k) && decide (e.2 = 0)
  | _, _ => false

theorem link_ok : linkOK startsAll endsAll = true := by decide +kernel

theorem first_ok : (match startsAll with | (k, ex, ey) :: _ => decide (k = 0) && decide (ex = Rk 0) && decide (ey = 0) | [] => false) = true := by decide +kernel

/-- integer weights per arc of circle k (denominator `DEN = 500·14·1024 = DENS2`). -/
def wt (k : Nat) : Int := if k = 0 then 284 else if k = 1 then 1101 else 5615
def DEN : Int := 7168000

def merge : Nat → List (Int × Int) → List (Int × Int) → List (Int × Int)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | f + 1, x :: xs, y :: ys => if x.1 ≤ y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys

def msort : Nat → List (Int × Int) → List (Int × Int)
  | 0, xs => xs
  | f + 1, xs =>
      match xs with
      | [] => []
      | [x] => [x]
      | _ =>
        let n := xs.length / 2
        merge (xs.length + 1) (msort f (xs.take n)) (msort f (xs.drop n))

def sortedSum : List (Int × Int) → Int → Int → Int
  | [], _, acc => acc
  | (v, w) :: rest, c, acc => sortedSum rest (c + w) (acc + v * ((c + w) * (c + w) - c * c))

def vals : List (Int × Int) := arcsAll.map (fun a => (a.Gmax, wt a.k))

def total : Int := sortedSum (msort 20 vals) 0 0

/-- conjunct 2 budget: total ≤ 11.2 (in units S·DEN²). -/
theorem total_ok : total ≤ 112 * DEN * DEN * S / 10 := by decide +kernel

theorem vals_length : vals.length = 3 * 1024 := by decide +kernel

/-- arc number `i` of `arcsAll` is `(k, j) = (i / 1024, i mod 1024)`. -/
theorem arcs_kj : arcsAll.map (fun a => (a.k, a.j)) =
    (List.range 3).flatMap (fun k => (List.range 1024).map (fun j => (k, j))) := by decide +kernel

end Work.Cert.Final
