/-
# `Work.Cert.conj2_cert2` — the conjunct-2 certificate on the 1024-grid

`Conj2Cert2` (Spec.lean, v4) asks for data `G E LS` describing, for each of the three circles `k ≤ 2`
and each of the `NARC2 = 1024` grid arcs `j < NARC2`, a chain of leaves from the grid point `E k j`
to `E k (j+1)` with all leaves `leafOK` and `Leaf.G ≤ G k j`, plus the weighted maximum-sum bound
`≤ 11.2` (units `S·DENS2²`).  This is the literal v4 transport of the proved 4096-grid assembly
`Submission/Work/Cert/conj2_cert.lean`:

* the 97 chunk chains `okC### : arcsOK2 endC###.1 endC###.2 arcsC### = true` (chunks `C000 … C096`,
  covering `Final.arcsAll`, 3072 arcs) are glued into one chain `chainAll : arcsChainTo2 (Rk 2) 0
  Final.arcsAll = true` using the generic append lemma `CJ2v.arcsChainTo2_append`; the 96 junction
  facts `lj###` come from `okC###` via `CJ2v.arcsOK2_last` together with a cheap `decide` on
  *metadata only* (no leaf evaluation, no scan of the arcs).
* `Final.arcs_kj` (with `CJ2Grid.range_map_div_mod`) gives `(arcAt i).k = i / 1024` and
  `(arcAt i).j = i % 1024`; `CJ2v.arcOK2_within` / `CJ2v.arcOK2_end` / `CJ2v.arcOK2_facts` then turn
  the chain facts into the per-`(k,j)` statements of `Conj2Cert2`.
* the sum: `CJ2Grid.sum_grid_reindex` flattens `Σ_{k,k'} Σ_{j,j'}` into `Σ_{a<3072} Σ_{b<3072}`,
  which is `CJ2.DsumFin Final.vals` (`CJ2.sum_range_eq_DsumFin` + `Final.vals_length`); the sorted
  evaluation lemmas of `CJ2Sum` identify it with `Final.total = Final.sortedSum (Final.msort 20 vals) 0 0`,
  and `Final.total_ok` finishes (`Final.DEN = DENS2 = 7168000`).

The data-free helper lemmas live in `Submission/Work/Cert/CJ2v/Basic.lean` (v4 copies of `CJ2/Gen`
and `CJ2/Helpers` with `4096 ↦ 1024`); the purely combinatorial material (`lastArc_append`,
`sum_range_eq_DsumFin`, `Dsum`/`msort`/`sortedSum`) is shared with the 4096-grid development and is
imported from `CJ2`.
-/

import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.Final
import Submission.Work.Cert.CJ2v.Basic
import Submission.Work.Cert.CJ2.Gen
import Submission.Work.Cert.CJ2.Helpers
import Submission.Work.Cert.CJ2Sum.sortedSum_eq_Dsum
import Submission.Work.Cert.CJ2Sum.Dsum_perm
import Submission.Work.Cert.CJ2Sum.msort_perm
import Submission.Work.Cert.CJ2Sum.msort_sorted
import Submission.Work.Cert.CJ2Sum.DsumFin_eq_Dsum
import Submission.Work.Cert.CJ2Grid.sum_grid_reindex
import Submission.Work.Cert.CJ2Grid.range_map_div_mod

set_option maxRecDepth 100000
set_option maxErrors 400
set_option maxHeartbeats 20000000

namespace Work.Cert

open Work.Cert.CJ2
open Work.Cert.CJ2v
open Work.Cert.Chunks

/-! ## the prefixes `pre{c}` = chunks `0 … c` (each chunk is appended on the right) -/

def pre000 : List ArcD := arcsC000
def pre001 : List ArcD := pre000 ++ arcsC001
def pre002 : List ArcD := pre001 ++ arcsC002
def pre003 : List ArcD := pre002 ++ arcsC003
def pre004 : List ArcD := pre003 ++ arcsC004
def pre005 : List ArcD := pre004 ++ arcsC005
def pre006 : List ArcD := pre005 ++ arcsC006
def pre007 : List ArcD := pre006 ++ arcsC007
def pre008 : List ArcD := pre007 ++ arcsC008
def pre009 : List ArcD := pre008 ++ arcsC009
def pre010 : List ArcD := pre009 ++ arcsC010
def pre011 : List ArcD := pre010 ++ arcsC011
def pre012 : List ArcD := pre011 ++ arcsC012
def pre013 : List ArcD := pre012 ++ arcsC013
def pre014 : List ArcD := pre013 ++ arcsC014
def pre015 : List ArcD := pre014 ++ arcsC015
def pre016 : List ArcD := pre015 ++ arcsC016
def pre017 : List ArcD := pre016 ++ arcsC017
def pre018 : List ArcD := pre017 ++ arcsC018
def pre019 : List ArcD := pre018 ++ arcsC019
def pre020 : List ArcD := pre019 ++ arcsC020
def pre021 : List ArcD := pre020 ++ arcsC021
def pre022 : List ArcD := pre021 ++ arcsC022
def pre023 : List ArcD := pre022 ++ arcsC023
def pre024 : List ArcD := pre023 ++ arcsC024
def pre025 : List ArcD := pre024 ++ arcsC025
def pre026 : List ArcD := pre025 ++ arcsC026
def pre027 : List ArcD := pre026 ++ arcsC027
def pre028 : List ArcD := pre027 ++ arcsC028
def pre029 : List ArcD := pre028 ++ arcsC029
def pre030 : List ArcD := pre029 ++ arcsC030
def pre031 : List ArcD := pre030 ++ arcsC031
def pre032 : List ArcD := pre031 ++ arcsC032
def pre033 : List ArcD := pre032 ++ arcsC033
def pre034 : List ArcD := pre033 ++ arcsC034
def pre035 : List ArcD := pre034 ++ arcsC035
def pre036 : List ArcD := pre035 ++ arcsC036
def pre037 : List ArcD := pre036 ++ arcsC037
def pre038 : List ArcD := pre037 ++ arcsC038
def pre039 : List ArcD := pre038 ++ arcsC039
def pre040 : List ArcD := pre039 ++ arcsC040
def pre041 : List ArcD := pre040 ++ arcsC041
def pre042 : List ArcD := pre041 ++ arcsC042
def pre043 : List ArcD := pre042 ++ arcsC043
def pre044 : List ArcD := pre043 ++ arcsC044
def pre045 : List ArcD := pre044 ++ arcsC045
def pre046 : List ArcD := pre045 ++ arcsC046
def pre047 : List ArcD := pre046 ++ arcsC047
def pre048 : List ArcD := pre047 ++ arcsC048
def pre049 : List ArcD := pre048 ++ arcsC049
def pre050 : List ArcD := pre049 ++ arcsC050
def pre051 : List ArcD := pre050 ++ arcsC051
def pre052 : List ArcD := pre051 ++ arcsC052
def pre053 : List ArcD := pre052 ++ arcsC053
def pre054 : List ArcD := pre053 ++ arcsC054
def pre055 : List ArcD := pre054 ++ arcsC055
def pre056 : List ArcD := pre055 ++ arcsC056
def pre057 : List ArcD := pre056 ++ arcsC057
def pre058 : List ArcD := pre057 ++ arcsC058
def pre059 : List ArcD := pre058 ++ arcsC059
def pre060 : List ArcD := pre059 ++ arcsC060
def pre061 : List ArcD := pre060 ++ arcsC061
def pre062 : List ArcD := pre061 ++ arcsC062
def pre063 : List ArcD := pre062 ++ arcsC063
def pre064 : List ArcD := pre063 ++ arcsC064
def pre065 : List ArcD := pre064 ++ arcsC065
def pre066 : List ArcD := pre065 ++ arcsC066
def pre067 : List ArcD := pre066 ++ arcsC067
def pre068 : List ArcD := pre067 ++ arcsC068
def pre069 : List ArcD := pre068 ++ arcsC069
def pre070 : List ArcD := pre069 ++ arcsC070
def pre071 : List ArcD := pre070 ++ arcsC071
def pre072 : List ArcD := pre071 ++ arcsC072
def pre073 : List ArcD := pre072 ++ arcsC073
def pre074 : List ArcD := pre073 ++ arcsC074
def pre075 : List ArcD := pre074 ++ arcsC075
def pre076 : List ArcD := pre075 ++ arcsC076
def pre077 : List ArcD := pre076 ++ arcsC077
def pre078 : List ArcD := pre077 ++ arcsC078
def pre079 : List ArcD := pre078 ++ arcsC079
def pre080 : List ArcD := pre079 ++ arcsC080
def pre081 : List ArcD := pre080 ++ arcsC081
def pre082 : List ArcD := pre081 ++ arcsC082
def pre083 : List ArcD := pre082 ++ arcsC083
def pre084 : List ArcD := pre083 ++ arcsC084
def pre085 : List ArcD := pre084 ++ arcsC085
def pre086 : List ArcD := pre085 ++ arcsC086
def pre087 : List ArcD := pre086 ++ arcsC087
def pre088 : List ArcD := pre087 ++ arcsC088
def pre089 : List ArcD := pre088 ++ arcsC089
def pre090 : List ArcD := pre089 ++ arcsC090
def pre091 : List ArcD := pre090 ++ arcsC091
def pre092 : List ArcD := pre091 ++ arcsC092
def pre093 : List ArcD := pre092 ++ arcsC093
def pre094 : List ArcD := pre093 ++ arcsC094
def pre095 : List ArcD := pre094 ++ arcsC095
def pre096 : List ArcD := pre095 ++ arcsC096

/-! ## junction facts (chunk `c` ends at the first grid point of chunk `c+1`) -/

theorem lj000 : linkStep2 (lastArc arcsC000) (headArc arcsC001) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC000) (headArc arcsC001) endC000.1 endC000.2
    (CJ2v.arcsOK2_last arcsC000 endC000.1 endC000.2 okC000 (List.cons_ne_nil _ _))
    (by decide)

theorem lj001 : linkStep2 (lastArc arcsC001) (headArc arcsC002) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC001) (headArc arcsC002) endC001.1 endC001.2
    (CJ2v.arcsOK2_last arcsC001 endC001.1 endC001.2 okC001 (List.cons_ne_nil _ _))
    (by decide)

theorem lj002 : linkStep2 (lastArc arcsC002) (headArc arcsC003) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC002) (headArc arcsC003) endC002.1 endC002.2
    (CJ2v.arcsOK2_last arcsC002 endC002.1 endC002.2 okC002 (List.cons_ne_nil _ _))
    (by decide)

theorem lj003 : linkStep2 (lastArc arcsC003) (headArc arcsC004) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC003) (headArc arcsC004) endC003.1 endC003.2
    (CJ2v.arcsOK2_last arcsC003 endC003.1 endC003.2 okC003 (List.cons_ne_nil _ _))
    (by decide)

theorem lj004 : linkStep2 (lastArc arcsC004) (headArc arcsC005) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC004) (headArc arcsC005) endC004.1 endC004.2
    (CJ2v.arcsOK2_last arcsC004 endC004.1 endC004.2 okC004 (List.cons_ne_nil _ _))
    (by decide)

theorem lj005 : linkStep2 (lastArc arcsC005) (headArc arcsC006) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC005) (headArc arcsC006) endC005.1 endC005.2
    (CJ2v.arcsOK2_last arcsC005 endC005.1 endC005.2 okC005 (List.cons_ne_nil _ _))
    (by decide)

theorem lj006 : linkStep2 (lastArc arcsC006) (headArc arcsC007) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC006) (headArc arcsC007) endC006.1 endC006.2
    (CJ2v.arcsOK2_last arcsC006 endC006.1 endC006.2 okC006 (List.cons_ne_nil _ _))
    (by decide)

theorem lj007 : linkStep2 (lastArc arcsC007) (headArc arcsC008) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC007) (headArc arcsC008) endC007.1 endC007.2
    (CJ2v.arcsOK2_last arcsC007 endC007.1 endC007.2 okC007 (List.cons_ne_nil _ _))
    (by decide)

theorem lj008 : linkStep2 (lastArc arcsC008) (headArc arcsC009) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC008) (headArc arcsC009) endC008.1 endC008.2
    (CJ2v.arcsOK2_last arcsC008 endC008.1 endC008.2 okC008 (List.cons_ne_nil _ _))
    (by decide)

theorem lj009 : linkStep2 (lastArc arcsC009) (headArc arcsC010) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC009) (headArc arcsC010) endC009.1 endC009.2
    (CJ2v.arcsOK2_last arcsC009 endC009.1 endC009.2 okC009 (List.cons_ne_nil _ _))
    (by decide)

theorem lj010 : linkStep2 (lastArc arcsC010) (headArc arcsC011) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC010) (headArc arcsC011) endC010.1 endC010.2
    (CJ2v.arcsOK2_last arcsC010 endC010.1 endC010.2 okC010 (List.cons_ne_nil _ _))
    (by decide)

theorem lj011 : linkStep2 (lastArc arcsC011) (headArc arcsC012) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC011) (headArc arcsC012) endC011.1 endC011.2
    (CJ2v.arcsOK2_last arcsC011 endC011.1 endC011.2 okC011 (List.cons_ne_nil _ _))
    (by decide)

theorem lj012 : linkStep2 (lastArc arcsC012) (headArc arcsC013) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC012) (headArc arcsC013) endC012.1 endC012.2
    (CJ2v.arcsOK2_last arcsC012 endC012.1 endC012.2 okC012 (List.cons_ne_nil _ _))
    (by decide)

theorem lj013 : linkStep2 (lastArc arcsC013) (headArc arcsC014) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC013) (headArc arcsC014) endC013.1 endC013.2
    (CJ2v.arcsOK2_last arcsC013 endC013.1 endC013.2 okC013 (List.cons_ne_nil _ _))
    (by decide)

theorem lj014 : linkStep2 (lastArc arcsC014) (headArc arcsC015) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC014) (headArc arcsC015) endC014.1 endC014.2
    (CJ2v.arcsOK2_last arcsC014 endC014.1 endC014.2 okC014 (List.cons_ne_nil _ _))
    (by decide)

theorem lj015 : linkStep2 (lastArc arcsC015) (headArc arcsC016) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC015) (headArc arcsC016) endC015.1 endC015.2
    (CJ2v.arcsOK2_last arcsC015 endC015.1 endC015.2 okC015 (List.cons_ne_nil _ _))
    (by decide)

theorem lj016 : linkStep2 (lastArc arcsC016) (headArc arcsC017) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC016) (headArc arcsC017) endC016.1 endC016.2
    (CJ2v.arcsOK2_last arcsC016 endC016.1 endC016.2 okC016 (List.cons_ne_nil _ _))
    (by decide)

theorem lj017 : linkStep2 (lastArc arcsC017) (headArc arcsC018) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC017) (headArc arcsC018) endC017.1 endC017.2
    (CJ2v.arcsOK2_last arcsC017 endC017.1 endC017.2 okC017 (List.cons_ne_nil _ _))
    (by decide)

theorem lj018 : linkStep2 (lastArc arcsC018) (headArc arcsC019) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC018) (headArc arcsC019) endC018.1 endC018.2
    (CJ2v.arcsOK2_last arcsC018 endC018.1 endC018.2 okC018 (List.cons_ne_nil _ _))
    (by decide)

theorem lj019 : linkStep2 (lastArc arcsC019) (headArc arcsC020) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC019) (headArc arcsC020) endC019.1 endC019.2
    (CJ2v.arcsOK2_last arcsC019 endC019.1 endC019.2 okC019 (List.cons_ne_nil _ _))
    (by decide)

theorem lj020 : linkStep2 (lastArc arcsC020) (headArc arcsC021) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC020) (headArc arcsC021) endC020.1 endC020.2
    (CJ2v.arcsOK2_last arcsC020 endC020.1 endC020.2 okC020 (List.cons_ne_nil _ _))
    (by decide)

theorem lj021 : linkStep2 (lastArc arcsC021) (headArc arcsC022) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC021) (headArc arcsC022) endC021.1 endC021.2
    (CJ2v.arcsOK2_last arcsC021 endC021.1 endC021.2 okC021 (List.cons_ne_nil _ _))
    (by decide)

theorem lj022 : linkStep2 (lastArc arcsC022) (headArc arcsC023) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC022) (headArc arcsC023) endC022.1 endC022.2
    (CJ2v.arcsOK2_last arcsC022 endC022.1 endC022.2 okC022 (List.cons_ne_nil _ _))
    (by decide)

theorem lj023 : linkStep2 (lastArc arcsC023) (headArc arcsC024) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC023) (headArc arcsC024) endC023.1 endC023.2
    (CJ2v.arcsOK2_last arcsC023 endC023.1 endC023.2 okC023 (List.cons_ne_nil _ _))
    (by decide)

theorem lj024 : linkStep2 (lastArc arcsC024) (headArc arcsC025) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC024) (headArc arcsC025) endC024.1 endC024.2
    (CJ2v.arcsOK2_last arcsC024 endC024.1 endC024.2 okC024 (List.cons_ne_nil _ _))
    (by decide)

theorem lj025 : linkStep2 (lastArc arcsC025) (headArc arcsC026) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC025) (headArc arcsC026) endC025.1 endC025.2
    (CJ2v.arcsOK2_last arcsC025 endC025.1 endC025.2 okC025 (List.cons_ne_nil _ _))
    (by decide)

theorem lj026 : linkStep2 (lastArc arcsC026) (headArc arcsC027) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC026) (headArc arcsC027) endC026.1 endC026.2
    (CJ2v.arcsOK2_last arcsC026 endC026.1 endC026.2 okC026 (List.cons_ne_nil _ _))
    (by decide)

theorem lj027 : linkStep2 (lastArc arcsC027) (headArc arcsC028) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC027) (headArc arcsC028) endC027.1 endC027.2
    (CJ2v.arcsOK2_last arcsC027 endC027.1 endC027.2 okC027 (List.cons_ne_nil _ _))
    (by decide)

theorem lj028 : linkStep2 (lastArc arcsC028) (headArc arcsC029) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC028) (headArc arcsC029) endC028.1 endC028.2
    (CJ2v.arcsOK2_last arcsC028 endC028.1 endC028.2 okC028 (List.cons_ne_nil _ _))
    (by decide)

theorem lj029 : linkStep2 (lastArc arcsC029) (headArc arcsC030) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC029) (headArc arcsC030) endC029.1 endC029.2
    (CJ2v.arcsOK2_last arcsC029 endC029.1 endC029.2 okC029 (List.cons_ne_nil _ _))
    (by decide)

theorem lj030 : linkStep2 (lastArc arcsC030) (headArc arcsC031) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC030) (headArc arcsC031) endC030.1 endC030.2
    (CJ2v.arcsOK2_last arcsC030 endC030.1 endC030.2 okC030 (List.cons_ne_nil _ _))
    (by decide)

theorem lj031 : linkStep2 (lastArc arcsC031) (headArc arcsC032) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC031) (headArc arcsC032) endC031.1 endC031.2
    (CJ2v.arcsOK2_last arcsC031 endC031.1 endC031.2 okC031 (List.cons_ne_nil _ _))
    (by decide)

theorem lj032 : linkStep2 (lastArc arcsC032) (headArc arcsC033) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC032) (headArc arcsC033) endC032.1 endC032.2
    (CJ2v.arcsOK2_last arcsC032 endC032.1 endC032.2 okC032 (List.cons_ne_nil _ _))
    (by decide)

theorem lj033 : linkStep2 (lastArc arcsC033) (headArc arcsC034) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC033) (headArc arcsC034) endC033.1 endC033.2
    (CJ2v.arcsOK2_last arcsC033 endC033.1 endC033.2 okC033 (List.cons_ne_nil _ _))
    (by decide)

theorem lj034 : linkStep2 (lastArc arcsC034) (headArc arcsC035) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC034) (headArc arcsC035) endC034.1 endC034.2
    (CJ2v.arcsOK2_last arcsC034 endC034.1 endC034.2 okC034 (List.cons_ne_nil _ _))
    (by decide)

theorem lj035 : linkStep2 (lastArc arcsC035) (headArc arcsC036) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC035) (headArc arcsC036) endC035.1 endC035.2
    (CJ2v.arcsOK2_last arcsC035 endC035.1 endC035.2 okC035 (List.cons_ne_nil _ _))
    (by decide)

theorem lj036 : linkStep2 (lastArc arcsC036) (headArc arcsC037) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC036) (headArc arcsC037) endC036.1 endC036.2
    (CJ2v.arcsOK2_last arcsC036 endC036.1 endC036.2 okC036 (List.cons_ne_nil _ _))
    (by decide)

theorem lj037 : linkStep2 (lastArc arcsC037) (headArc arcsC038) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC037) (headArc arcsC038) endC037.1 endC037.2
    (CJ2v.arcsOK2_last arcsC037 endC037.1 endC037.2 okC037 (List.cons_ne_nil _ _))
    (by decide)

theorem lj038 : linkStep2 (lastArc arcsC038) (headArc arcsC039) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC038) (headArc arcsC039) endC038.1 endC038.2
    (CJ2v.arcsOK2_last arcsC038 endC038.1 endC038.2 okC038 (List.cons_ne_nil _ _))
    (by decide)

theorem lj039 : linkStep2 (lastArc arcsC039) (headArc arcsC040) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC039) (headArc arcsC040) endC039.1 endC039.2
    (CJ2v.arcsOK2_last arcsC039 endC039.1 endC039.2 okC039 (List.cons_ne_nil _ _))
    (by decide)

theorem lj040 : linkStep2 (lastArc arcsC040) (headArc arcsC041) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC040) (headArc arcsC041) endC040.1 endC040.2
    (CJ2v.arcsOK2_last arcsC040 endC040.1 endC040.2 okC040 (List.cons_ne_nil _ _))
    (by decide)

theorem lj041 : linkStep2 (lastArc arcsC041) (headArc arcsC042) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC041) (headArc arcsC042) endC041.1 endC041.2
    (CJ2v.arcsOK2_last arcsC041 endC041.1 endC041.2 okC041 (List.cons_ne_nil _ _))
    (by decide)

theorem lj042 : linkStep2 (lastArc arcsC042) (headArc arcsC043) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC042) (headArc arcsC043) endC042.1 endC042.2
    (CJ2v.arcsOK2_last arcsC042 endC042.1 endC042.2 okC042 (List.cons_ne_nil _ _))
    (by decide)

theorem lj043 : linkStep2 (lastArc arcsC043) (headArc arcsC044) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC043) (headArc arcsC044) endC043.1 endC043.2
    (CJ2v.arcsOK2_last arcsC043 endC043.1 endC043.2 okC043 (List.cons_ne_nil _ _))
    (by decide)

theorem lj044 : linkStep2 (lastArc arcsC044) (headArc arcsC045) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC044) (headArc arcsC045) endC044.1 endC044.2
    (CJ2v.arcsOK2_last arcsC044 endC044.1 endC044.2 okC044 (List.cons_ne_nil _ _))
    (by decide)

theorem lj045 : linkStep2 (lastArc arcsC045) (headArc arcsC046) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC045) (headArc arcsC046) endC045.1 endC045.2
    (CJ2v.arcsOK2_last arcsC045 endC045.1 endC045.2 okC045 (List.cons_ne_nil _ _))
    (by decide)

theorem lj046 : linkStep2 (lastArc arcsC046) (headArc arcsC047) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC046) (headArc arcsC047) endC046.1 endC046.2
    (CJ2v.arcsOK2_last arcsC046 endC046.1 endC046.2 okC046 (List.cons_ne_nil _ _))
    (by decide)

theorem lj047 : linkStep2 (lastArc arcsC047) (headArc arcsC048) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC047) (headArc arcsC048) endC047.1 endC047.2
    (CJ2v.arcsOK2_last arcsC047 endC047.1 endC047.2 okC047 (List.cons_ne_nil _ _))
    (by decide)

theorem lj048 : linkStep2 (lastArc arcsC048) (headArc arcsC049) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC048) (headArc arcsC049) endC048.1 endC048.2
    (CJ2v.arcsOK2_last arcsC048 endC048.1 endC048.2 okC048 (List.cons_ne_nil _ _))
    (by decide)

theorem lj049 : linkStep2 (lastArc arcsC049) (headArc arcsC050) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC049) (headArc arcsC050) endC049.1 endC049.2
    (CJ2v.arcsOK2_last arcsC049 endC049.1 endC049.2 okC049 (List.cons_ne_nil _ _))
    (by decide)

theorem lj050 : linkStep2 (lastArc arcsC050) (headArc arcsC051) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC050) (headArc arcsC051) endC050.1 endC050.2
    (CJ2v.arcsOK2_last arcsC050 endC050.1 endC050.2 okC050 (List.cons_ne_nil _ _))
    (by decide)

theorem lj051 : linkStep2 (lastArc arcsC051) (headArc arcsC052) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC051) (headArc arcsC052) endC051.1 endC051.2
    (CJ2v.arcsOK2_last arcsC051 endC051.1 endC051.2 okC051 (List.cons_ne_nil _ _))
    (by decide)

theorem lj052 : linkStep2 (lastArc arcsC052) (headArc arcsC053) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC052) (headArc arcsC053) endC052.1 endC052.2
    (CJ2v.arcsOK2_last arcsC052 endC052.1 endC052.2 okC052 (List.cons_ne_nil _ _))
    (by decide)

theorem lj053 : linkStep2 (lastArc arcsC053) (headArc arcsC054) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC053) (headArc arcsC054) endC053.1 endC053.2
    (CJ2v.arcsOK2_last arcsC053 endC053.1 endC053.2 okC053 (List.cons_ne_nil _ _))
    (by decide)

theorem lj054 : linkStep2 (lastArc arcsC054) (headArc arcsC055) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC054) (headArc arcsC055) endC054.1 endC054.2
    (CJ2v.arcsOK2_last arcsC054 endC054.1 endC054.2 okC054 (List.cons_ne_nil _ _))
    (by decide)

theorem lj055 : linkStep2 (lastArc arcsC055) (headArc arcsC056) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC055) (headArc arcsC056) endC055.1 endC055.2
    (CJ2v.arcsOK2_last arcsC055 endC055.1 endC055.2 okC055 (List.cons_ne_nil _ _))
    (by decide)

theorem lj056 : linkStep2 (lastArc arcsC056) (headArc arcsC057) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC056) (headArc arcsC057) endC056.1 endC056.2
    (CJ2v.arcsOK2_last arcsC056 endC056.1 endC056.2 okC056 (List.cons_ne_nil _ _))
    (by decide)

theorem lj057 : linkStep2 (lastArc arcsC057) (headArc arcsC058) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC057) (headArc arcsC058) endC057.1 endC057.2
    (CJ2v.arcsOK2_last arcsC057 endC057.1 endC057.2 okC057 (List.cons_ne_nil _ _))
    (by decide)

theorem lj058 : linkStep2 (lastArc arcsC058) (headArc arcsC059) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC058) (headArc arcsC059) endC058.1 endC058.2
    (CJ2v.arcsOK2_last arcsC058 endC058.1 endC058.2 okC058 (List.cons_ne_nil _ _))
    (by decide)

theorem lj059 : linkStep2 (lastArc arcsC059) (headArc arcsC060) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC059) (headArc arcsC060) endC059.1 endC059.2
    (CJ2v.arcsOK2_last arcsC059 endC059.1 endC059.2 okC059 (List.cons_ne_nil _ _))
    (by decide)

theorem lj060 : linkStep2 (lastArc arcsC060) (headArc arcsC061) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC060) (headArc arcsC061) endC060.1 endC060.2
    (CJ2v.arcsOK2_last arcsC060 endC060.1 endC060.2 okC060 (List.cons_ne_nil _ _))
    (by decide)

theorem lj061 : linkStep2 (lastArc arcsC061) (headArc arcsC062) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC061) (headArc arcsC062) endC061.1 endC061.2
    (CJ2v.arcsOK2_last arcsC061 endC061.1 endC061.2 okC061 (List.cons_ne_nil _ _))
    (by decide)

theorem lj062 : linkStep2 (lastArc arcsC062) (headArc arcsC063) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC062) (headArc arcsC063) endC062.1 endC062.2
    (CJ2v.arcsOK2_last arcsC062 endC062.1 endC062.2 okC062 (List.cons_ne_nil _ _))
    (by decide)

theorem lj063 : linkStep2 (lastArc arcsC063) (headArc arcsC064) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC063) (headArc arcsC064) endC063.1 endC063.2
    (CJ2v.arcsOK2_last arcsC063 endC063.1 endC063.2 okC063 (List.cons_ne_nil _ _))
    (by decide)

theorem lj064 : linkStep2 (lastArc arcsC064) (headArc arcsC065) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC064) (headArc arcsC065) endC064.1 endC064.2
    (CJ2v.arcsOK2_last arcsC064 endC064.1 endC064.2 okC064 (List.cons_ne_nil _ _))
    (by decide)

theorem lj065 : linkStep2 (lastArc arcsC065) (headArc arcsC066) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC065) (headArc arcsC066) endC065.1 endC065.2
    (CJ2v.arcsOK2_last arcsC065 endC065.1 endC065.2 okC065 (List.cons_ne_nil _ _))
    (by decide)

theorem lj066 : linkStep2 (lastArc arcsC066) (headArc arcsC067) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC066) (headArc arcsC067) endC066.1 endC066.2
    (CJ2v.arcsOK2_last arcsC066 endC066.1 endC066.2 okC066 (List.cons_ne_nil _ _))
    (by decide)

theorem lj067 : linkStep2 (lastArc arcsC067) (headArc arcsC068) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC067) (headArc arcsC068) endC067.1 endC067.2
    (CJ2v.arcsOK2_last arcsC067 endC067.1 endC067.2 okC067 (List.cons_ne_nil _ _))
    (by decide)

theorem lj068 : linkStep2 (lastArc arcsC068) (headArc arcsC069) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC068) (headArc arcsC069) endC068.1 endC068.2
    (CJ2v.arcsOK2_last arcsC068 endC068.1 endC068.2 okC068 (List.cons_ne_nil _ _))
    (by decide)

theorem lj069 : linkStep2 (lastArc arcsC069) (headArc arcsC070) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC069) (headArc arcsC070) endC069.1 endC069.2
    (CJ2v.arcsOK2_last arcsC069 endC069.1 endC069.2 okC069 (List.cons_ne_nil _ _))
    (by decide)

theorem lj070 : linkStep2 (lastArc arcsC070) (headArc arcsC071) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC070) (headArc arcsC071) endC070.1 endC070.2
    (CJ2v.arcsOK2_last arcsC070 endC070.1 endC070.2 okC070 (List.cons_ne_nil _ _))
    (by decide)

theorem lj071 : linkStep2 (lastArc arcsC071) (headArc arcsC072) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC071) (headArc arcsC072) endC071.1 endC071.2
    (CJ2v.arcsOK2_last arcsC071 endC071.1 endC071.2 okC071 (List.cons_ne_nil _ _))
    (by decide)

theorem lj072 : linkStep2 (lastArc arcsC072) (headArc arcsC073) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC072) (headArc arcsC073) endC072.1 endC072.2
    (CJ2v.arcsOK2_last arcsC072 endC072.1 endC072.2 okC072 (List.cons_ne_nil _ _))
    (by decide)

theorem lj073 : linkStep2 (lastArc arcsC073) (headArc arcsC074) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC073) (headArc arcsC074) endC073.1 endC073.2
    (CJ2v.arcsOK2_last arcsC073 endC073.1 endC073.2 okC073 (List.cons_ne_nil _ _))
    (by decide)

theorem lj074 : linkStep2 (lastArc arcsC074) (headArc arcsC075) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC074) (headArc arcsC075) endC074.1 endC074.2
    (CJ2v.arcsOK2_last arcsC074 endC074.1 endC074.2 okC074 (List.cons_ne_nil _ _))
    (by decide)

theorem lj075 : linkStep2 (lastArc arcsC075) (headArc arcsC076) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC075) (headArc arcsC076) endC075.1 endC075.2
    (CJ2v.arcsOK2_last arcsC075 endC075.1 endC075.2 okC075 (List.cons_ne_nil _ _))
    (by decide)

theorem lj076 : linkStep2 (lastArc arcsC076) (headArc arcsC077) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC076) (headArc arcsC077) endC076.1 endC076.2
    (CJ2v.arcsOK2_last arcsC076 endC076.1 endC076.2 okC076 (List.cons_ne_nil _ _))
    (by decide)

theorem lj077 : linkStep2 (lastArc arcsC077) (headArc arcsC078) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC077) (headArc arcsC078) endC077.1 endC077.2
    (CJ2v.arcsOK2_last arcsC077 endC077.1 endC077.2 okC077 (List.cons_ne_nil _ _))
    (by decide)

theorem lj078 : linkStep2 (lastArc arcsC078) (headArc arcsC079) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC078) (headArc arcsC079) endC078.1 endC078.2
    (CJ2v.arcsOK2_last arcsC078 endC078.1 endC078.2 okC078 (List.cons_ne_nil _ _))
    (by decide)

theorem lj079 : linkStep2 (lastArc arcsC079) (headArc arcsC080) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC079) (headArc arcsC080) endC079.1 endC079.2
    (CJ2v.arcsOK2_last arcsC079 endC079.1 endC079.2 okC079 (List.cons_ne_nil _ _))
    (by decide)

theorem lj080 : linkStep2 (lastArc arcsC080) (headArc arcsC081) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC080) (headArc arcsC081) endC080.1 endC080.2
    (CJ2v.arcsOK2_last arcsC080 endC080.1 endC080.2 okC080 (List.cons_ne_nil _ _))
    (by decide)

theorem lj081 : linkStep2 (lastArc arcsC081) (headArc arcsC082) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC081) (headArc arcsC082) endC081.1 endC081.2
    (CJ2v.arcsOK2_last arcsC081 endC081.1 endC081.2 okC081 (List.cons_ne_nil _ _))
    (by decide)

theorem lj082 : linkStep2 (lastArc arcsC082) (headArc arcsC083) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC082) (headArc arcsC083) endC082.1 endC082.2
    (CJ2v.arcsOK2_last arcsC082 endC082.1 endC082.2 okC082 (List.cons_ne_nil _ _))
    (by decide)

theorem lj083 : linkStep2 (lastArc arcsC083) (headArc arcsC084) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC083) (headArc arcsC084) endC083.1 endC083.2
    (CJ2v.arcsOK2_last arcsC083 endC083.1 endC083.2 okC083 (List.cons_ne_nil _ _))
    (by decide)

theorem lj084 : linkStep2 (lastArc arcsC084) (headArc arcsC085) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC084) (headArc arcsC085) endC084.1 endC084.2
    (CJ2v.arcsOK2_last arcsC084 endC084.1 endC084.2 okC084 (List.cons_ne_nil _ _))
    (by decide)

theorem lj085 : linkStep2 (lastArc arcsC085) (headArc arcsC086) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC085) (headArc arcsC086) endC085.1 endC085.2
    (CJ2v.arcsOK2_last arcsC085 endC085.1 endC085.2 okC085 (List.cons_ne_nil _ _))
    (by decide)

theorem lj086 : linkStep2 (lastArc arcsC086) (headArc arcsC087) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC086) (headArc arcsC087) endC086.1 endC086.2
    (CJ2v.arcsOK2_last arcsC086 endC086.1 endC086.2 okC086 (List.cons_ne_nil _ _))
    (by decide)

theorem lj087 : linkStep2 (lastArc arcsC087) (headArc arcsC088) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC087) (headArc arcsC088) endC087.1 endC087.2
    (CJ2v.arcsOK2_last arcsC087 endC087.1 endC087.2 okC087 (List.cons_ne_nil _ _))
    (by decide)

theorem lj088 : linkStep2 (lastArc arcsC088) (headArc arcsC089) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC088) (headArc arcsC089) endC088.1 endC088.2
    (CJ2v.arcsOK2_last arcsC088 endC088.1 endC088.2 okC088 (List.cons_ne_nil _ _))
    (by decide)

theorem lj089 : linkStep2 (lastArc arcsC089) (headArc arcsC090) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC089) (headArc arcsC090) endC089.1 endC089.2
    (CJ2v.arcsOK2_last arcsC089 endC089.1 endC089.2 okC089 (List.cons_ne_nil _ _))
    (by decide)

theorem lj090 : linkStep2 (lastArc arcsC090) (headArc arcsC091) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC090) (headArc arcsC091) endC090.1 endC090.2
    (CJ2v.arcsOK2_last arcsC090 endC090.1 endC090.2 okC090 (List.cons_ne_nil _ _))
    (by decide)

theorem lj091 : linkStep2 (lastArc arcsC091) (headArc arcsC092) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC091) (headArc arcsC092) endC091.1 endC091.2
    (CJ2v.arcsOK2_last arcsC091 endC091.1 endC091.2 okC091 (List.cons_ne_nil _ _))
    (by decide)

theorem lj092 : linkStep2 (lastArc arcsC092) (headArc arcsC093) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC092) (headArc arcsC093) endC092.1 endC092.2
    (CJ2v.arcsOK2_last arcsC092 endC092.1 endC092.2 okC092 (List.cons_ne_nil _ _))
    (by decide)

theorem lj093 : linkStep2 (lastArc arcsC093) (headArc arcsC094) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC093) (headArc arcsC094) endC093.1 endC093.2
    (CJ2v.arcsOK2_last arcsC093 endC093.1 endC093.2 okC093 (List.cons_ne_nil _ _))
    (by decide)

theorem lj094 : linkStep2 (lastArc arcsC094) (headArc arcsC095) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC094) (headArc arcsC095) endC094.1 endC094.2
    (CJ2v.arcsOK2_last arcsC094 endC094.1 endC094.2 okC094 (List.cons_ne_nil _ _))
    (by decide)

theorem lj095 : linkStep2 (lastArc arcsC095) (headArc arcsC096) = true :=
  CJ2v.linkStep2_of_arcOK2 (lastArc arcsC095) (headArc arcsC096) endC095.1 endC095.2
    (CJ2v.arcsOK2_last arcsC095 endC095.1 endC095.2 okC095 (List.cons_ne_nil _ _))
    (by decide)

/-! ## gluing the chunk chains -/

theorem chain000 : arcsChainTo2 endC000.1 endC000.2 pre000 = true :=
  CJ2v.arcsChainTo2_of_arcsOK2 arcsC000 _ _ okC000

theorem chain001 : arcsChainTo2 endC001.1 endC001.2 pre001 = true := by
  have hlast : lastArc pre000 = lastArc arcsC000 := rfl
  show arcsChainTo2 endC001.1 endC001.2 (pre000 ++ arcsC001) = true
  exact CJ2v.arcsChainTo2_append pre000 arcsC001 endC000.1 endC000.2 endC001.1 endC001.2
    chain000 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC001 _ _ okC001) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj000)

theorem chain002 : arcsChainTo2 endC002.1 endC002.2 pre002 = true := by
  have hlast : lastArc pre001 = lastArc arcsC001 := by
    show lastArc (pre000 ++ arcsC001) = lastArc arcsC001
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC002.1 endC002.2 (pre001 ++ arcsC002) = true
  exact CJ2v.arcsChainTo2_append pre001 arcsC002 endC001.1 endC001.2 endC002.1 endC002.2
    chain001 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC002 _ _ okC002) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj001)

theorem chain003 : arcsChainTo2 endC003.1 endC003.2 pre003 = true := by
  have hlast : lastArc pre002 = lastArc arcsC002 := by
    show lastArc (pre001 ++ arcsC002) = lastArc arcsC002
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC003.1 endC003.2 (pre002 ++ arcsC003) = true
  exact CJ2v.arcsChainTo2_append pre002 arcsC003 endC002.1 endC002.2 endC003.1 endC003.2
    chain002 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC003 _ _ okC003) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj002)

theorem chain004 : arcsChainTo2 endC004.1 endC004.2 pre004 = true := by
  have hlast : lastArc pre003 = lastArc arcsC003 := by
    show lastArc (pre002 ++ arcsC003) = lastArc arcsC003
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC004.1 endC004.2 (pre003 ++ arcsC004) = true
  exact CJ2v.arcsChainTo2_append pre003 arcsC004 endC003.1 endC003.2 endC004.1 endC004.2
    chain003 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC004 _ _ okC004) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj003)

theorem chain005 : arcsChainTo2 endC005.1 endC005.2 pre005 = true := by
  have hlast : lastArc pre004 = lastArc arcsC004 := by
    show lastArc (pre003 ++ arcsC004) = lastArc arcsC004
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC005.1 endC005.2 (pre004 ++ arcsC005) = true
  exact CJ2v.arcsChainTo2_append pre004 arcsC005 endC004.1 endC004.2 endC005.1 endC005.2
    chain004 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC005 _ _ okC005) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj004)

theorem chain006 : arcsChainTo2 endC006.1 endC006.2 pre006 = true := by
  have hlast : lastArc pre005 = lastArc arcsC005 := by
    show lastArc (pre004 ++ arcsC005) = lastArc arcsC005
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC006.1 endC006.2 (pre005 ++ arcsC006) = true
  exact CJ2v.arcsChainTo2_append pre005 arcsC006 endC005.1 endC005.2 endC006.1 endC006.2
    chain005 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC006 _ _ okC006) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj005)

theorem chain007 : arcsChainTo2 endC007.1 endC007.2 pre007 = true := by
  have hlast : lastArc pre006 = lastArc arcsC006 := by
    show lastArc (pre005 ++ arcsC006) = lastArc arcsC006
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC007.1 endC007.2 (pre006 ++ arcsC007) = true
  exact CJ2v.arcsChainTo2_append pre006 arcsC007 endC006.1 endC006.2 endC007.1 endC007.2
    chain006 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC007 _ _ okC007) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj006)

theorem chain008 : arcsChainTo2 endC008.1 endC008.2 pre008 = true := by
  have hlast : lastArc pre007 = lastArc arcsC007 := by
    show lastArc (pre006 ++ arcsC007) = lastArc arcsC007
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC008.1 endC008.2 (pre007 ++ arcsC008) = true
  exact CJ2v.arcsChainTo2_append pre007 arcsC008 endC007.1 endC007.2 endC008.1 endC008.2
    chain007 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC008 _ _ okC008) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj007)

theorem chain009 : arcsChainTo2 endC009.1 endC009.2 pre009 = true := by
  have hlast : lastArc pre008 = lastArc arcsC008 := by
    show lastArc (pre007 ++ arcsC008) = lastArc arcsC008
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC009.1 endC009.2 (pre008 ++ arcsC009) = true
  exact CJ2v.arcsChainTo2_append pre008 arcsC009 endC008.1 endC008.2 endC009.1 endC009.2
    chain008 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC009 _ _ okC009) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj008)

theorem chain010 : arcsChainTo2 endC010.1 endC010.2 pre010 = true := by
  have hlast : lastArc pre009 = lastArc arcsC009 := by
    show lastArc (pre008 ++ arcsC009) = lastArc arcsC009
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC010.1 endC010.2 (pre009 ++ arcsC010) = true
  exact CJ2v.arcsChainTo2_append pre009 arcsC010 endC009.1 endC009.2 endC010.1 endC010.2
    chain009 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC010 _ _ okC010) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj009)

theorem chain011 : arcsChainTo2 endC011.1 endC011.2 pre011 = true := by
  have hlast : lastArc pre010 = lastArc arcsC010 := by
    show lastArc (pre009 ++ arcsC010) = lastArc arcsC010
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC011.1 endC011.2 (pre010 ++ arcsC011) = true
  exact CJ2v.arcsChainTo2_append pre010 arcsC011 endC010.1 endC010.2 endC011.1 endC011.2
    chain010 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC011 _ _ okC011) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj010)

theorem chain012 : arcsChainTo2 endC012.1 endC012.2 pre012 = true := by
  have hlast : lastArc pre011 = lastArc arcsC011 := by
    show lastArc (pre010 ++ arcsC011) = lastArc arcsC011
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC012.1 endC012.2 (pre011 ++ arcsC012) = true
  exact CJ2v.arcsChainTo2_append pre011 arcsC012 endC011.1 endC011.2 endC012.1 endC012.2
    chain011 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC012 _ _ okC012) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj011)

theorem chain013 : arcsChainTo2 endC013.1 endC013.2 pre013 = true := by
  have hlast : lastArc pre012 = lastArc arcsC012 := by
    show lastArc (pre011 ++ arcsC012) = lastArc arcsC012
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC013.1 endC013.2 (pre012 ++ arcsC013) = true
  exact CJ2v.arcsChainTo2_append pre012 arcsC013 endC012.1 endC012.2 endC013.1 endC013.2
    chain012 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC013 _ _ okC013) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj012)

theorem chain014 : arcsChainTo2 endC014.1 endC014.2 pre014 = true := by
  have hlast : lastArc pre013 = lastArc arcsC013 := by
    show lastArc (pre012 ++ arcsC013) = lastArc arcsC013
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC014.1 endC014.2 (pre013 ++ arcsC014) = true
  exact CJ2v.arcsChainTo2_append pre013 arcsC014 endC013.1 endC013.2 endC014.1 endC014.2
    chain013 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC014 _ _ okC014) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj013)

theorem chain015 : arcsChainTo2 endC015.1 endC015.2 pre015 = true := by
  have hlast : lastArc pre014 = lastArc arcsC014 := by
    show lastArc (pre013 ++ arcsC014) = lastArc arcsC014
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC015.1 endC015.2 (pre014 ++ arcsC015) = true
  exact CJ2v.arcsChainTo2_append pre014 arcsC015 endC014.1 endC014.2 endC015.1 endC015.2
    chain014 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC015 _ _ okC015) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj014)

theorem chain016 : arcsChainTo2 endC016.1 endC016.2 pre016 = true := by
  have hlast : lastArc pre015 = lastArc arcsC015 := by
    show lastArc (pre014 ++ arcsC015) = lastArc arcsC015
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC016.1 endC016.2 (pre015 ++ arcsC016) = true
  exact CJ2v.arcsChainTo2_append pre015 arcsC016 endC015.1 endC015.2 endC016.1 endC016.2
    chain015 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC016 _ _ okC016) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj015)

theorem chain017 : arcsChainTo2 endC017.1 endC017.2 pre017 = true := by
  have hlast : lastArc pre016 = lastArc arcsC016 := by
    show lastArc (pre015 ++ arcsC016) = lastArc arcsC016
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC017.1 endC017.2 (pre016 ++ arcsC017) = true
  exact CJ2v.arcsChainTo2_append pre016 arcsC017 endC016.1 endC016.2 endC017.1 endC017.2
    chain016 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC017 _ _ okC017) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj016)

theorem chain018 : arcsChainTo2 endC018.1 endC018.2 pre018 = true := by
  have hlast : lastArc pre017 = lastArc arcsC017 := by
    show lastArc (pre016 ++ arcsC017) = lastArc arcsC017
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC018.1 endC018.2 (pre017 ++ arcsC018) = true
  exact CJ2v.arcsChainTo2_append pre017 arcsC018 endC017.1 endC017.2 endC018.1 endC018.2
    chain017 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC018 _ _ okC018) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj017)

theorem chain019 : arcsChainTo2 endC019.1 endC019.2 pre019 = true := by
  have hlast : lastArc pre018 = lastArc arcsC018 := by
    show lastArc (pre017 ++ arcsC018) = lastArc arcsC018
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC019.1 endC019.2 (pre018 ++ arcsC019) = true
  exact CJ2v.arcsChainTo2_append pre018 arcsC019 endC018.1 endC018.2 endC019.1 endC019.2
    chain018 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC019 _ _ okC019) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj018)

theorem chain020 : arcsChainTo2 endC020.1 endC020.2 pre020 = true := by
  have hlast : lastArc pre019 = lastArc arcsC019 := by
    show lastArc (pre018 ++ arcsC019) = lastArc arcsC019
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC020.1 endC020.2 (pre019 ++ arcsC020) = true
  exact CJ2v.arcsChainTo2_append pre019 arcsC020 endC019.1 endC019.2 endC020.1 endC020.2
    chain019 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC020 _ _ okC020) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj019)

theorem chain021 : arcsChainTo2 endC021.1 endC021.2 pre021 = true := by
  have hlast : lastArc pre020 = lastArc arcsC020 := by
    show lastArc (pre019 ++ arcsC020) = lastArc arcsC020
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC021.1 endC021.2 (pre020 ++ arcsC021) = true
  exact CJ2v.arcsChainTo2_append pre020 arcsC021 endC020.1 endC020.2 endC021.1 endC021.2
    chain020 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC021 _ _ okC021) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj020)

theorem chain022 : arcsChainTo2 endC022.1 endC022.2 pre022 = true := by
  have hlast : lastArc pre021 = lastArc arcsC021 := by
    show lastArc (pre020 ++ arcsC021) = lastArc arcsC021
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC022.1 endC022.2 (pre021 ++ arcsC022) = true
  exact CJ2v.arcsChainTo2_append pre021 arcsC022 endC021.1 endC021.2 endC022.1 endC022.2
    chain021 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC022 _ _ okC022) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj021)

theorem chain023 : arcsChainTo2 endC023.1 endC023.2 pre023 = true := by
  have hlast : lastArc pre022 = lastArc arcsC022 := by
    show lastArc (pre021 ++ arcsC022) = lastArc arcsC022
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC023.1 endC023.2 (pre022 ++ arcsC023) = true
  exact CJ2v.arcsChainTo2_append pre022 arcsC023 endC022.1 endC022.2 endC023.1 endC023.2
    chain022 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC023 _ _ okC023) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj022)

theorem chain024 : arcsChainTo2 endC024.1 endC024.2 pre024 = true := by
  have hlast : lastArc pre023 = lastArc arcsC023 := by
    show lastArc (pre022 ++ arcsC023) = lastArc arcsC023
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC024.1 endC024.2 (pre023 ++ arcsC024) = true
  exact CJ2v.arcsChainTo2_append pre023 arcsC024 endC023.1 endC023.2 endC024.1 endC024.2
    chain023 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC024 _ _ okC024) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj023)

theorem chain025 : arcsChainTo2 endC025.1 endC025.2 pre025 = true := by
  have hlast : lastArc pre024 = lastArc arcsC024 := by
    show lastArc (pre023 ++ arcsC024) = lastArc arcsC024
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC025.1 endC025.2 (pre024 ++ arcsC025) = true
  exact CJ2v.arcsChainTo2_append pre024 arcsC025 endC024.1 endC024.2 endC025.1 endC025.2
    chain024 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC025 _ _ okC025) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj024)

theorem chain026 : arcsChainTo2 endC026.1 endC026.2 pre026 = true := by
  have hlast : lastArc pre025 = lastArc arcsC025 := by
    show lastArc (pre024 ++ arcsC025) = lastArc arcsC025
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC026.1 endC026.2 (pre025 ++ arcsC026) = true
  exact CJ2v.arcsChainTo2_append pre025 arcsC026 endC025.1 endC025.2 endC026.1 endC026.2
    chain025 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC026 _ _ okC026) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj025)

theorem chain027 : arcsChainTo2 endC027.1 endC027.2 pre027 = true := by
  have hlast : lastArc pre026 = lastArc arcsC026 := by
    show lastArc (pre025 ++ arcsC026) = lastArc arcsC026
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC027.1 endC027.2 (pre026 ++ arcsC027) = true
  exact CJ2v.arcsChainTo2_append pre026 arcsC027 endC026.1 endC026.2 endC027.1 endC027.2
    chain026 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC027 _ _ okC027) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj026)

theorem chain028 : arcsChainTo2 endC028.1 endC028.2 pre028 = true := by
  have hlast : lastArc pre027 = lastArc arcsC027 := by
    show lastArc (pre026 ++ arcsC027) = lastArc arcsC027
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC028.1 endC028.2 (pre027 ++ arcsC028) = true
  exact CJ2v.arcsChainTo2_append pre027 arcsC028 endC027.1 endC027.2 endC028.1 endC028.2
    chain027 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC028 _ _ okC028) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj027)

theorem chain029 : arcsChainTo2 endC029.1 endC029.2 pre029 = true := by
  have hlast : lastArc pre028 = lastArc arcsC028 := by
    show lastArc (pre027 ++ arcsC028) = lastArc arcsC028
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC029.1 endC029.2 (pre028 ++ arcsC029) = true
  exact CJ2v.arcsChainTo2_append pre028 arcsC029 endC028.1 endC028.2 endC029.1 endC029.2
    chain028 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC029 _ _ okC029) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj028)

theorem chain030 : arcsChainTo2 endC030.1 endC030.2 pre030 = true := by
  have hlast : lastArc pre029 = lastArc arcsC029 := by
    show lastArc (pre028 ++ arcsC029) = lastArc arcsC029
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC030.1 endC030.2 (pre029 ++ arcsC030) = true
  exact CJ2v.arcsChainTo2_append pre029 arcsC030 endC029.1 endC029.2 endC030.1 endC030.2
    chain029 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC030 _ _ okC030) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj029)

theorem chain031 : arcsChainTo2 endC031.1 endC031.2 pre031 = true := by
  have hlast : lastArc pre030 = lastArc arcsC030 := by
    show lastArc (pre029 ++ arcsC030) = lastArc arcsC030
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC031.1 endC031.2 (pre030 ++ arcsC031) = true
  exact CJ2v.arcsChainTo2_append pre030 arcsC031 endC030.1 endC030.2 endC031.1 endC031.2
    chain030 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC031 _ _ okC031) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj030)

theorem chain032 : arcsChainTo2 endC032.1 endC032.2 pre032 = true := by
  have hlast : lastArc pre031 = lastArc arcsC031 := by
    show lastArc (pre030 ++ arcsC031) = lastArc arcsC031
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC032.1 endC032.2 (pre031 ++ arcsC032) = true
  exact CJ2v.arcsChainTo2_append pre031 arcsC032 endC031.1 endC031.2 endC032.1 endC032.2
    chain031 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC032 _ _ okC032) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj031)

theorem chain033 : arcsChainTo2 endC033.1 endC033.2 pre033 = true := by
  have hlast : lastArc pre032 = lastArc arcsC032 := by
    show lastArc (pre031 ++ arcsC032) = lastArc arcsC032
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC033.1 endC033.2 (pre032 ++ arcsC033) = true
  exact CJ2v.arcsChainTo2_append pre032 arcsC033 endC032.1 endC032.2 endC033.1 endC033.2
    chain032 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC033 _ _ okC033) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj032)

theorem chain034 : arcsChainTo2 endC034.1 endC034.2 pre034 = true := by
  have hlast : lastArc pre033 = lastArc arcsC033 := by
    show lastArc (pre032 ++ arcsC033) = lastArc arcsC033
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC034.1 endC034.2 (pre033 ++ arcsC034) = true
  exact CJ2v.arcsChainTo2_append pre033 arcsC034 endC033.1 endC033.2 endC034.1 endC034.2
    chain033 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC034 _ _ okC034) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj033)

theorem chain035 : arcsChainTo2 endC035.1 endC035.2 pre035 = true := by
  have hlast : lastArc pre034 = lastArc arcsC034 := by
    show lastArc (pre033 ++ arcsC034) = lastArc arcsC034
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC035.1 endC035.2 (pre034 ++ arcsC035) = true
  exact CJ2v.arcsChainTo2_append pre034 arcsC035 endC034.1 endC034.2 endC035.1 endC035.2
    chain034 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC035 _ _ okC035) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj034)

theorem chain036 : arcsChainTo2 endC036.1 endC036.2 pre036 = true := by
  have hlast : lastArc pre035 = lastArc arcsC035 := by
    show lastArc (pre034 ++ arcsC035) = lastArc arcsC035
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC036.1 endC036.2 (pre035 ++ arcsC036) = true
  exact CJ2v.arcsChainTo2_append pre035 arcsC036 endC035.1 endC035.2 endC036.1 endC036.2
    chain035 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC036 _ _ okC036) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj035)

theorem chain037 : arcsChainTo2 endC037.1 endC037.2 pre037 = true := by
  have hlast : lastArc pre036 = lastArc arcsC036 := by
    show lastArc (pre035 ++ arcsC036) = lastArc arcsC036
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC037.1 endC037.2 (pre036 ++ arcsC037) = true
  exact CJ2v.arcsChainTo2_append pre036 arcsC037 endC036.1 endC036.2 endC037.1 endC037.2
    chain036 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC037 _ _ okC037) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj036)

theorem chain038 : arcsChainTo2 endC038.1 endC038.2 pre038 = true := by
  have hlast : lastArc pre037 = lastArc arcsC037 := by
    show lastArc (pre036 ++ arcsC037) = lastArc arcsC037
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC038.1 endC038.2 (pre037 ++ arcsC038) = true
  exact CJ2v.arcsChainTo2_append pre037 arcsC038 endC037.1 endC037.2 endC038.1 endC038.2
    chain037 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC038 _ _ okC038) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj037)

theorem chain039 : arcsChainTo2 endC039.1 endC039.2 pre039 = true := by
  have hlast : lastArc pre038 = lastArc arcsC038 := by
    show lastArc (pre037 ++ arcsC038) = lastArc arcsC038
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC039.1 endC039.2 (pre038 ++ arcsC039) = true
  exact CJ2v.arcsChainTo2_append pre038 arcsC039 endC038.1 endC038.2 endC039.1 endC039.2
    chain038 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC039 _ _ okC039) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj038)

theorem chain040 : arcsChainTo2 endC040.1 endC040.2 pre040 = true := by
  have hlast : lastArc pre039 = lastArc arcsC039 := by
    show lastArc (pre038 ++ arcsC039) = lastArc arcsC039
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC040.1 endC040.2 (pre039 ++ arcsC040) = true
  exact CJ2v.arcsChainTo2_append pre039 arcsC040 endC039.1 endC039.2 endC040.1 endC040.2
    chain039 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC040 _ _ okC040) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj039)

theorem chain041 : arcsChainTo2 endC041.1 endC041.2 pre041 = true := by
  have hlast : lastArc pre040 = lastArc arcsC040 := by
    show lastArc (pre039 ++ arcsC040) = lastArc arcsC040
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC041.1 endC041.2 (pre040 ++ arcsC041) = true
  exact CJ2v.arcsChainTo2_append pre040 arcsC041 endC040.1 endC040.2 endC041.1 endC041.2
    chain040 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC041 _ _ okC041) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj040)

theorem chain042 : arcsChainTo2 endC042.1 endC042.2 pre042 = true := by
  have hlast : lastArc pre041 = lastArc arcsC041 := by
    show lastArc (pre040 ++ arcsC041) = lastArc arcsC041
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC042.1 endC042.2 (pre041 ++ arcsC042) = true
  exact CJ2v.arcsChainTo2_append pre041 arcsC042 endC041.1 endC041.2 endC042.1 endC042.2
    chain041 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC042 _ _ okC042) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj041)

theorem chain043 : arcsChainTo2 endC043.1 endC043.2 pre043 = true := by
  have hlast : lastArc pre042 = lastArc arcsC042 := by
    show lastArc (pre041 ++ arcsC042) = lastArc arcsC042
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC043.1 endC043.2 (pre042 ++ arcsC043) = true
  exact CJ2v.arcsChainTo2_append pre042 arcsC043 endC042.1 endC042.2 endC043.1 endC043.2
    chain042 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC043 _ _ okC043) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj042)

theorem chain044 : arcsChainTo2 endC044.1 endC044.2 pre044 = true := by
  have hlast : lastArc pre043 = lastArc arcsC043 := by
    show lastArc (pre042 ++ arcsC043) = lastArc arcsC043
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC044.1 endC044.2 (pre043 ++ arcsC044) = true
  exact CJ2v.arcsChainTo2_append pre043 arcsC044 endC043.1 endC043.2 endC044.1 endC044.2
    chain043 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC044 _ _ okC044) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj043)

theorem chain045 : arcsChainTo2 endC045.1 endC045.2 pre045 = true := by
  have hlast : lastArc pre044 = lastArc arcsC044 := by
    show lastArc (pre043 ++ arcsC044) = lastArc arcsC044
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC045.1 endC045.2 (pre044 ++ arcsC045) = true
  exact CJ2v.arcsChainTo2_append pre044 arcsC045 endC044.1 endC044.2 endC045.1 endC045.2
    chain044 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC045 _ _ okC045) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj044)

theorem chain046 : arcsChainTo2 endC046.1 endC046.2 pre046 = true := by
  have hlast : lastArc pre045 = lastArc arcsC045 := by
    show lastArc (pre044 ++ arcsC045) = lastArc arcsC045
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC046.1 endC046.2 (pre045 ++ arcsC046) = true
  exact CJ2v.arcsChainTo2_append pre045 arcsC046 endC045.1 endC045.2 endC046.1 endC046.2
    chain045 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC046 _ _ okC046) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj045)

theorem chain047 : arcsChainTo2 endC047.1 endC047.2 pre047 = true := by
  have hlast : lastArc pre046 = lastArc arcsC046 := by
    show lastArc (pre045 ++ arcsC046) = lastArc arcsC046
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC047.1 endC047.2 (pre046 ++ arcsC047) = true
  exact CJ2v.arcsChainTo2_append pre046 arcsC047 endC046.1 endC046.2 endC047.1 endC047.2
    chain046 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC047 _ _ okC047) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj046)

theorem chain048 : arcsChainTo2 endC048.1 endC048.2 pre048 = true := by
  have hlast : lastArc pre047 = lastArc arcsC047 := by
    show lastArc (pre046 ++ arcsC047) = lastArc arcsC047
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC048.1 endC048.2 (pre047 ++ arcsC048) = true
  exact CJ2v.arcsChainTo2_append pre047 arcsC048 endC047.1 endC047.2 endC048.1 endC048.2
    chain047 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC048 _ _ okC048) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj047)

theorem chain049 : arcsChainTo2 endC049.1 endC049.2 pre049 = true := by
  have hlast : lastArc pre048 = lastArc arcsC048 := by
    show lastArc (pre047 ++ arcsC048) = lastArc arcsC048
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC049.1 endC049.2 (pre048 ++ arcsC049) = true
  exact CJ2v.arcsChainTo2_append pre048 arcsC049 endC048.1 endC048.2 endC049.1 endC049.2
    chain048 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC049 _ _ okC049) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj048)

theorem chain050 : arcsChainTo2 endC050.1 endC050.2 pre050 = true := by
  have hlast : lastArc pre049 = lastArc arcsC049 := by
    show lastArc (pre048 ++ arcsC049) = lastArc arcsC049
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC050.1 endC050.2 (pre049 ++ arcsC050) = true
  exact CJ2v.arcsChainTo2_append pre049 arcsC050 endC049.1 endC049.2 endC050.1 endC050.2
    chain049 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC050 _ _ okC050) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj049)

theorem chain051 : arcsChainTo2 endC051.1 endC051.2 pre051 = true := by
  have hlast : lastArc pre050 = lastArc arcsC050 := by
    show lastArc (pre049 ++ arcsC050) = lastArc arcsC050
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC051.1 endC051.2 (pre050 ++ arcsC051) = true
  exact CJ2v.arcsChainTo2_append pre050 arcsC051 endC050.1 endC050.2 endC051.1 endC051.2
    chain050 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC051 _ _ okC051) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj050)

theorem chain052 : arcsChainTo2 endC052.1 endC052.2 pre052 = true := by
  have hlast : lastArc pre051 = lastArc arcsC051 := by
    show lastArc (pre050 ++ arcsC051) = lastArc arcsC051
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC052.1 endC052.2 (pre051 ++ arcsC052) = true
  exact CJ2v.arcsChainTo2_append pre051 arcsC052 endC051.1 endC051.2 endC052.1 endC052.2
    chain051 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC052 _ _ okC052) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj051)

theorem chain053 : arcsChainTo2 endC053.1 endC053.2 pre053 = true := by
  have hlast : lastArc pre052 = lastArc arcsC052 := by
    show lastArc (pre051 ++ arcsC052) = lastArc arcsC052
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC053.1 endC053.2 (pre052 ++ arcsC053) = true
  exact CJ2v.arcsChainTo2_append pre052 arcsC053 endC052.1 endC052.2 endC053.1 endC053.2
    chain052 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC053 _ _ okC053) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj052)

theorem chain054 : arcsChainTo2 endC054.1 endC054.2 pre054 = true := by
  have hlast : lastArc pre053 = lastArc arcsC053 := by
    show lastArc (pre052 ++ arcsC053) = lastArc arcsC053
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC054.1 endC054.2 (pre053 ++ arcsC054) = true
  exact CJ2v.arcsChainTo2_append pre053 arcsC054 endC053.1 endC053.2 endC054.1 endC054.2
    chain053 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC054 _ _ okC054) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj053)

theorem chain055 : arcsChainTo2 endC055.1 endC055.2 pre055 = true := by
  have hlast : lastArc pre054 = lastArc arcsC054 := by
    show lastArc (pre053 ++ arcsC054) = lastArc arcsC054
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC055.1 endC055.2 (pre054 ++ arcsC055) = true
  exact CJ2v.arcsChainTo2_append pre054 arcsC055 endC054.1 endC054.2 endC055.1 endC055.2
    chain054 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC055 _ _ okC055) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj054)

theorem chain056 : arcsChainTo2 endC056.1 endC056.2 pre056 = true := by
  have hlast : lastArc pre055 = lastArc arcsC055 := by
    show lastArc (pre054 ++ arcsC055) = lastArc arcsC055
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC056.1 endC056.2 (pre055 ++ arcsC056) = true
  exact CJ2v.arcsChainTo2_append pre055 arcsC056 endC055.1 endC055.2 endC056.1 endC056.2
    chain055 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC056 _ _ okC056) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj055)

theorem chain057 : arcsChainTo2 endC057.1 endC057.2 pre057 = true := by
  have hlast : lastArc pre056 = lastArc arcsC056 := by
    show lastArc (pre055 ++ arcsC056) = lastArc arcsC056
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC057.1 endC057.2 (pre056 ++ arcsC057) = true
  exact CJ2v.arcsChainTo2_append pre056 arcsC057 endC056.1 endC056.2 endC057.1 endC057.2
    chain056 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC057 _ _ okC057) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj056)

theorem chain058 : arcsChainTo2 endC058.1 endC058.2 pre058 = true := by
  have hlast : lastArc pre057 = lastArc arcsC057 := by
    show lastArc (pre056 ++ arcsC057) = lastArc arcsC057
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC058.1 endC058.2 (pre057 ++ arcsC058) = true
  exact CJ2v.arcsChainTo2_append pre057 arcsC058 endC057.1 endC057.2 endC058.1 endC058.2
    chain057 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC058 _ _ okC058) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj057)

theorem chain059 : arcsChainTo2 endC059.1 endC059.2 pre059 = true := by
  have hlast : lastArc pre058 = lastArc arcsC058 := by
    show lastArc (pre057 ++ arcsC058) = lastArc arcsC058
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC059.1 endC059.2 (pre058 ++ arcsC059) = true
  exact CJ2v.arcsChainTo2_append pre058 arcsC059 endC058.1 endC058.2 endC059.1 endC059.2
    chain058 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC059 _ _ okC059) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj058)

theorem chain060 : arcsChainTo2 endC060.1 endC060.2 pre060 = true := by
  have hlast : lastArc pre059 = lastArc arcsC059 := by
    show lastArc (pre058 ++ arcsC059) = lastArc arcsC059
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC060.1 endC060.2 (pre059 ++ arcsC060) = true
  exact CJ2v.arcsChainTo2_append pre059 arcsC060 endC059.1 endC059.2 endC060.1 endC060.2
    chain059 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC060 _ _ okC060) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj059)

theorem chain061 : arcsChainTo2 endC061.1 endC061.2 pre061 = true := by
  have hlast : lastArc pre060 = lastArc arcsC060 := by
    show lastArc (pre059 ++ arcsC060) = lastArc arcsC060
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC061.1 endC061.2 (pre060 ++ arcsC061) = true
  exact CJ2v.arcsChainTo2_append pre060 arcsC061 endC060.1 endC060.2 endC061.1 endC061.2
    chain060 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC061 _ _ okC061) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj060)

theorem chain062 : arcsChainTo2 endC062.1 endC062.2 pre062 = true := by
  have hlast : lastArc pre061 = lastArc arcsC061 := by
    show lastArc (pre060 ++ arcsC061) = lastArc arcsC061
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC062.1 endC062.2 (pre061 ++ arcsC062) = true
  exact CJ2v.arcsChainTo2_append pre061 arcsC062 endC061.1 endC061.2 endC062.1 endC062.2
    chain061 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC062 _ _ okC062) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj061)

theorem chain063 : arcsChainTo2 endC063.1 endC063.2 pre063 = true := by
  have hlast : lastArc pre062 = lastArc arcsC062 := by
    show lastArc (pre061 ++ arcsC062) = lastArc arcsC062
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC063.1 endC063.2 (pre062 ++ arcsC063) = true
  exact CJ2v.arcsChainTo2_append pre062 arcsC063 endC062.1 endC062.2 endC063.1 endC063.2
    chain062 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC063 _ _ okC063) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj062)

theorem chain064 : arcsChainTo2 endC064.1 endC064.2 pre064 = true := by
  have hlast : lastArc pre063 = lastArc arcsC063 := by
    show lastArc (pre062 ++ arcsC063) = lastArc arcsC063
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC064.1 endC064.2 (pre063 ++ arcsC064) = true
  exact CJ2v.arcsChainTo2_append pre063 arcsC064 endC063.1 endC063.2 endC064.1 endC064.2
    chain063 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC064 _ _ okC064) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj063)

theorem chain065 : arcsChainTo2 endC065.1 endC065.2 pre065 = true := by
  have hlast : lastArc pre064 = lastArc arcsC064 := by
    show lastArc (pre063 ++ arcsC064) = lastArc arcsC064
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC065.1 endC065.2 (pre064 ++ arcsC065) = true
  exact CJ2v.arcsChainTo2_append pre064 arcsC065 endC064.1 endC064.2 endC065.1 endC065.2
    chain064 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC065 _ _ okC065) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj064)

theorem chain066 : arcsChainTo2 endC066.1 endC066.2 pre066 = true := by
  have hlast : lastArc pre065 = lastArc arcsC065 := by
    show lastArc (pre064 ++ arcsC065) = lastArc arcsC065
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC066.1 endC066.2 (pre065 ++ arcsC066) = true
  exact CJ2v.arcsChainTo2_append pre065 arcsC066 endC065.1 endC065.2 endC066.1 endC066.2
    chain065 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC066 _ _ okC066) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj065)

theorem chain067 : arcsChainTo2 endC067.1 endC067.2 pre067 = true := by
  have hlast : lastArc pre066 = lastArc arcsC066 := by
    show lastArc (pre065 ++ arcsC066) = lastArc arcsC066
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC067.1 endC067.2 (pre066 ++ arcsC067) = true
  exact CJ2v.arcsChainTo2_append pre066 arcsC067 endC066.1 endC066.2 endC067.1 endC067.2
    chain066 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC067 _ _ okC067) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj066)

theorem chain068 : arcsChainTo2 endC068.1 endC068.2 pre068 = true := by
  have hlast : lastArc pre067 = lastArc arcsC067 := by
    show lastArc (pre066 ++ arcsC067) = lastArc arcsC067
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC068.1 endC068.2 (pre067 ++ arcsC068) = true
  exact CJ2v.arcsChainTo2_append pre067 arcsC068 endC067.1 endC067.2 endC068.1 endC068.2
    chain067 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC068 _ _ okC068) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj067)

theorem chain069 : arcsChainTo2 endC069.1 endC069.2 pre069 = true := by
  have hlast : lastArc pre068 = lastArc arcsC068 := by
    show lastArc (pre067 ++ arcsC068) = lastArc arcsC068
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC069.1 endC069.2 (pre068 ++ arcsC069) = true
  exact CJ2v.arcsChainTo2_append pre068 arcsC069 endC068.1 endC068.2 endC069.1 endC069.2
    chain068 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC069 _ _ okC069) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj068)

theorem chain070 : arcsChainTo2 endC070.1 endC070.2 pre070 = true := by
  have hlast : lastArc pre069 = lastArc arcsC069 := by
    show lastArc (pre068 ++ arcsC069) = lastArc arcsC069
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC070.1 endC070.2 (pre069 ++ arcsC070) = true
  exact CJ2v.arcsChainTo2_append pre069 arcsC070 endC069.1 endC069.2 endC070.1 endC070.2
    chain069 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC070 _ _ okC070) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj069)

theorem chain071 : arcsChainTo2 endC071.1 endC071.2 pre071 = true := by
  have hlast : lastArc pre070 = lastArc arcsC070 := by
    show lastArc (pre069 ++ arcsC070) = lastArc arcsC070
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC071.1 endC071.2 (pre070 ++ arcsC071) = true
  exact CJ2v.arcsChainTo2_append pre070 arcsC071 endC070.1 endC070.2 endC071.1 endC071.2
    chain070 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC071 _ _ okC071) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj070)

theorem chain072 : arcsChainTo2 endC072.1 endC072.2 pre072 = true := by
  have hlast : lastArc pre071 = lastArc arcsC071 := by
    show lastArc (pre070 ++ arcsC071) = lastArc arcsC071
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC072.1 endC072.2 (pre071 ++ arcsC072) = true
  exact CJ2v.arcsChainTo2_append pre071 arcsC072 endC071.1 endC071.2 endC072.1 endC072.2
    chain071 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC072 _ _ okC072) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj071)

theorem chain073 : arcsChainTo2 endC073.1 endC073.2 pre073 = true := by
  have hlast : lastArc pre072 = lastArc arcsC072 := by
    show lastArc (pre071 ++ arcsC072) = lastArc arcsC072
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC073.1 endC073.2 (pre072 ++ arcsC073) = true
  exact CJ2v.arcsChainTo2_append pre072 arcsC073 endC072.1 endC072.2 endC073.1 endC073.2
    chain072 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC073 _ _ okC073) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj072)

theorem chain074 : arcsChainTo2 endC074.1 endC074.2 pre074 = true := by
  have hlast : lastArc pre073 = lastArc arcsC073 := by
    show lastArc (pre072 ++ arcsC073) = lastArc arcsC073
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC074.1 endC074.2 (pre073 ++ arcsC074) = true
  exact CJ2v.arcsChainTo2_append pre073 arcsC074 endC073.1 endC073.2 endC074.1 endC074.2
    chain073 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC074 _ _ okC074) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj073)

theorem chain075 : arcsChainTo2 endC075.1 endC075.2 pre075 = true := by
  have hlast : lastArc pre074 = lastArc arcsC074 := by
    show lastArc (pre073 ++ arcsC074) = lastArc arcsC074
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC075.1 endC075.2 (pre074 ++ arcsC075) = true
  exact CJ2v.arcsChainTo2_append pre074 arcsC075 endC074.1 endC074.2 endC075.1 endC075.2
    chain074 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC075 _ _ okC075) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj074)

theorem chain076 : arcsChainTo2 endC076.1 endC076.2 pre076 = true := by
  have hlast : lastArc pre075 = lastArc arcsC075 := by
    show lastArc (pre074 ++ arcsC075) = lastArc arcsC075
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC076.1 endC076.2 (pre075 ++ arcsC076) = true
  exact CJ2v.arcsChainTo2_append pre075 arcsC076 endC075.1 endC075.2 endC076.1 endC076.2
    chain075 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC076 _ _ okC076) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj075)

theorem chain077 : arcsChainTo2 endC077.1 endC077.2 pre077 = true := by
  have hlast : lastArc pre076 = lastArc arcsC076 := by
    show lastArc (pre075 ++ arcsC076) = lastArc arcsC076
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC077.1 endC077.2 (pre076 ++ arcsC077) = true
  exact CJ2v.arcsChainTo2_append pre076 arcsC077 endC076.1 endC076.2 endC077.1 endC077.2
    chain076 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC077 _ _ okC077) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj076)

theorem chain078 : arcsChainTo2 endC078.1 endC078.2 pre078 = true := by
  have hlast : lastArc pre077 = lastArc arcsC077 := by
    show lastArc (pre076 ++ arcsC077) = lastArc arcsC077
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC078.1 endC078.2 (pre077 ++ arcsC078) = true
  exact CJ2v.arcsChainTo2_append pre077 arcsC078 endC077.1 endC077.2 endC078.1 endC078.2
    chain077 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC078 _ _ okC078) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj077)

theorem chain079 : arcsChainTo2 endC079.1 endC079.2 pre079 = true := by
  have hlast : lastArc pre078 = lastArc arcsC078 := by
    show lastArc (pre077 ++ arcsC078) = lastArc arcsC078
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC079.1 endC079.2 (pre078 ++ arcsC079) = true
  exact CJ2v.arcsChainTo2_append pre078 arcsC079 endC078.1 endC078.2 endC079.1 endC079.2
    chain078 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC079 _ _ okC079) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj078)

theorem chain080 : arcsChainTo2 endC080.1 endC080.2 pre080 = true := by
  have hlast : lastArc pre079 = lastArc arcsC079 := by
    show lastArc (pre078 ++ arcsC079) = lastArc arcsC079
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC080.1 endC080.2 (pre079 ++ arcsC080) = true
  exact CJ2v.arcsChainTo2_append pre079 arcsC080 endC079.1 endC079.2 endC080.1 endC080.2
    chain079 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC080 _ _ okC080) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj079)

theorem chain081 : arcsChainTo2 endC081.1 endC081.2 pre081 = true := by
  have hlast : lastArc pre080 = lastArc arcsC080 := by
    show lastArc (pre079 ++ arcsC080) = lastArc arcsC080
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC081.1 endC081.2 (pre080 ++ arcsC081) = true
  exact CJ2v.arcsChainTo2_append pre080 arcsC081 endC080.1 endC080.2 endC081.1 endC081.2
    chain080 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC081 _ _ okC081) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj080)

theorem chain082 : arcsChainTo2 endC082.1 endC082.2 pre082 = true := by
  have hlast : lastArc pre081 = lastArc arcsC081 := by
    show lastArc (pre080 ++ arcsC081) = lastArc arcsC081
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC082.1 endC082.2 (pre081 ++ arcsC082) = true
  exact CJ2v.arcsChainTo2_append pre081 arcsC082 endC081.1 endC081.2 endC082.1 endC082.2
    chain081 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC082 _ _ okC082) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj081)

theorem chain083 : arcsChainTo2 endC083.1 endC083.2 pre083 = true := by
  have hlast : lastArc pre082 = lastArc arcsC082 := by
    show lastArc (pre081 ++ arcsC082) = lastArc arcsC082
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC083.1 endC083.2 (pre082 ++ arcsC083) = true
  exact CJ2v.arcsChainTo2_append pre082 arcsC083 endC082.1 endC082.2 endC083.1 endC083.2
    chain082 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC083 _ _ okC083) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj082)

theorem chain084 : arcsChainTo2 endC084.1 endC084.2 pre084 = true := by
  have hlast : lastArc pre083 = lastArc arcsC083 := by
    show lastArc (pre082 ++ arcsC083) = lastArc arcsC083
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC084.1 endC084.2 (pre083 ++ arcsC084) = true
  exact CJ2v.arcsChainTo2_append pre083 arcsC084 endC083.1 endC083.2 endC084.1 endC084.2
    chain083 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC084 _ _ okC084) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj083)

theorem chain085 : arcsChainTo2 endC085.1 endC085.2 pre085 = true := by
  have hlast : lastArc pre084 = lastArc arcsC084 := by
    show lastArc (pre083 ++ arcsC084) = lastArc arcsC084
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC085.1 endC085.2 (pre084 ++ arcsC085) = true
  exact CJ2v.arcsChainTo2_append pre084 arcsC085 endC084.1 endC084.2 endC085.1 endC085.2
    chain084 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC085 _ _ okC085) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj084)

theorem chain086 : arcsChainTo2 endC086.1 endC086.2 pre086 = true := by
  have hlast : lastArc pre085 = lastArc arcsC085 := by
    show lastArc (pre084 ++ arcsC085) = lastArc arcsC085
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC086.1 endC086.2 (pre085 ++ arcsC086) = true
  exact CJ2v.arcsChainTo2_append pre085 arcsC086 endC085.1 endC085.2 endC086.1 endC086.2
    chain085 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC086 _ _ okC086) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj085)

theorem chain087 : arcsChainTo2 endC087.1 endC087.2 pre087 = true := by
  have hlast : lastArc pre086 = lastArc arcsC086 := by
    show lastArc (pre085 ++ arcsC086) = lastArc arcsC086
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC087.1 endC087.2 (pre086 ++ arcsC087) = true
  exact CJ2v.arcsChainTo2_append pre086 arcsC087 endC086.1 endC086.2 endC087.1 endC087.2
    chain086 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC087 _ _ okC087) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj086)

theorem chain088 : arcsChainTo2 endC088.1 endC088.2 pre088 = true := by
  have hlast : lastArc pre087 = lastArc arcsC087 := by
    show lastArc (pre086 ++ arcsC087) = lastArc arcsC087
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC088.1 endC088.2 (pre087 ++ arcsC088) = true
  exact CJ2v.arcsChainTo2_append pre087 arcsC088 endC087.1 endC087.2 endC088.1 endC088.2
    chain087 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC088 _ _ okC088) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj087)

theorem chain089 : arcsChainTo2 endC089.1 endC089.2 pre089 = true := by
  have hlast : lastArc pre088 = lastArc arcsC088 := by
    show lastArc (pre087 ++ arcsC088) = lastArc arcsC088
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC089.1 endC089.2 (pre088 ++ arcsC089) = true
  exact CJ2v.arcsChainTo2_append pre088 arcsC089 endC088.1 endC088.2 endC089.1 endC089.2
    chain088 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC089 _ _ okC089) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj088)

theorem chain090 : arcsChainTo2 endC090.1 endC090.2 pre090 = true := by
  have hlast : lastArc pre089 = lastArc arcsC089 := by
    show lastArc (pre088 ++ arcsC089) = lastArc arcsC089
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC090.1 endC090.2 (pre089 ++ arcsC090) = true
  exact CJ2v.arcsChainTo2_append pre089 arcsC090 endC089.1 endC089.2 endC090.1 endC090.2
    chain089 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC090 _ _ okC090) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj089)

theorem chain091 : arcsChainTo2 endC091.1 endC091.2 pre091 = true := by
  have hlast : lastArc pre090 = lastArc arcsC090 := by
    show lastArc (pre089 ++ arcsC090) = lastArc arcsC090
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC091.1 endC091.2 (pre090 ++ arcsC091) = true
  exact CJ2v.arcsChainTo2_append pre090 arcsC091 endC090.1 endC090.2 endC091.1 endC091.2
    chain090 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC091 _ _ okC091) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj090)

theorem chain092 : arcsChainTo2 endC092.1 endC092.2 pre092 = true := by
  have hlast : lastArc pre091 = lastArc arcsC091 := by
    show lastArc (pre090 ++ arcsC091) = lastArc arcsC091
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC092.1 endC092.2 (pre091 ++ arcsC092) = true
  exact CJ2v.arcsChainTo2_append pre091 arcsC092 endC091.1 endC091.2 endC092.1 endC092.2
    chain091 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC092 _ _ okC092) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj091)

theorem chain093 : arcsChainTo2 endC093.1 endC093.2 pre093 = true := by
  have hlast : lastArc pre092 = lastArc arcsC092 := by
    show lastArc (pre091 ++ arcsC092) = lastArc arcsC092
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC093.1 endC093.2 (pre092 ++ arcsC093) = true
  exact CJ2v.arcsChainTo2_append pre092 arcsC093 endC092.1 endC092.2 endC093.1 endC093.2
    chain092 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC093 _ _ okC093) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj092)

theorem chain094 : arcsChainTo2 endC094.1 endC094.2 pre094 = true := by
  have hlast : lastArc pre093 = lastArc arcsC093 := by
    show lastArc (pre092 ++ arcsC093) = lastArc arcsC093
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC094.1 endC094.2 (pre093 ++ arcsC094) = true
  exact CJ2v.arcsChainTo2_append pre093 arcsC094 endC093.1 endC093.2 endC094.1 endC094.2
    chain093 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC094 _ _ okC094) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj093)

theorem chain095 : arcsChainTo2 endC095.1 endC095.2 pre095 = true := by
  have hlast : lastArc pre094 = lastArc arcsC094 := by
    show lastArc (pre093 ++ arcsC094) = lastArc arcsC094
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC095.1 endC095.2 (pre094 ++ arcsC095) = true
  exact CJ2v.arcsChainTo2_append pre094 arcsC095 endC094.1 endC094.2 endC095.1 endC095.2
    chain094 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC095 _ _ okC095) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj094)

theorem chain096 : arcsChainTo2 endC096.1 endC096.2 pre096 = true := by
  have hlast : lastArc pre095 = lastArc arcsC095 := by
    show lastArc (pre094 ++ arcsC095) = lastArc arcsC095
    exact lastArc_append _ _ (List.cons_ne_nil _ _)
  show arcsChainTo2 endC096.1 endC096.2 (pre095 ++ arcsC096) = true
  exact CJ2v.arcsChainTo2_append pre095 arcsC096 endC095.1 endC095.2 endC096.1 endC096.2
    chain095 (CJ2v.arcsChainTo2_of_arcsOK2 arcsC096 _ _ okC096) (List.cons_ne_nil _ _)
    (by rw [hlast]; exact lj095)

theorem pre096_eq : pre096 = Final.arcsAll := rfl

theorem chainAll : arcsChainTo2 (Rk 2) 0 Final.arcsAll = true := by
  have h := chain096
  rw [show endC096.1 = Rk 2 from by decide, show endC096.2 = 0 from by decide] at h
  rwa [pre096_eq] at h

theorem arcsAll_length : Final.arcsAll.length = 3072 := by
  have h := Final.vals_length
  simpa [Final.vals] using h

theorem arcsAll_map_kj :
    Final.arcsAll.map (fun a => (a.k, a.j))
      = (List.range 3072).map (fun i => (i / 1024, i % 1024)) := by
  rw [Final.arcs_kj, ← CJ2Grid.range_map_div_mod 3 1024 (by norm_num)]

/-- the arc at flat index `i` (circles `k = 0,1,2` occupy `1024k ≤ i < 1024(k+1)`). -/
def arcAt (i : ℕ) : ArcD := Final.arcsAll.getD i dummyArc

theorem arcAt_linkStep2 (i : ℕ) (hi : i + 1 < 3072) :
    linkStep2 (arcAt i) (arcAt (i + 1)) = true := by
  have hi' : i + 1 < Final.arcsAll.length := by rw [arcsAll_length]; exact hi
  have h := CJ2v.arcsChainTo2_next_getD Final.arcsAll (Rk 2) 0 chainAll i hi'
  simpa [arcAt] using h

theorem arcAt_k (i : ℕ) (hi : i < 3072) : (arcAt i).k = i / 1024 := by
  have hi' : i < Final.arcsAll.length := by rw [arcsAll_length]; exact hi
  rw [arcAt, List.getD_eq_getElem Final.arcsAll dummyArc (n := i) (hn := hi')]
  exact (CJ2v.kAt_of_map Final.arcsAll 3072 arcsAll_map_kj i hi').1

theorem arcAt_j (i : ℕ) (hi : i < 3072) : (arcAt i).j = i % 1024 := by
  have hi' : i < Final.arcsAll.length := by rw [arcsAll_length]; exact hi
  rw [arcAt, List.getD_eq_getElem Final.arcsAll dummyArc (n := i) (hn := hi')]
  exact (CJ2v.kAt_of_map Final.arcsAll 3072 arcsAll_map_kj i hi').2

theorem arcAt_lastOK : arcOK2 (arcAt 3071) (Rk 2) 0 = true := by
  have h := CJ2v.arcsChainTo2_last_getD Final.arcsAll (Rk 2) 0 3071 chainAll
    (by rw [arcsAll_length])
  simpa [arcAt] using h

/-! ## the candidate data for `Conj2Cert2` -/

/-- the maximum log bound over the leaves of arc `(k,j)`. -/
def Gc (k j : ℕ) : ℤ := (arcAt (1024 * k + j)).Gmax

/-- the grid point at the start of arc `(k,j)` (`(Rk k, 0)` for `j = 1024`). -/
def Ec (k j : ℕ) : ℤ × ℤ :=
  if j < 1024 then ((arcAt (1024 * k + j)).Ex, (arcAt (1024 * k + j)).Ey) else (Rk k, 0)

/-- the leaves of arc `(k,j)`. -/
def LSc (k j : ℕ) : List Leaf := (arcAt (1024 * k + j)).leaves

theorem arcAt_0_Ex : (arcAt 0).Ex = Rk 0 := by decide
theorem arcAt_0_Ey : (arcAt 0).Ey = 0 := by decide
theorem arcAt_1024_Ex : (arcAt 1024).Ex = Rk 1 := by decide
theorem arcAt_1024_Ey : (arcAt 1024).Ey = 0 := by decide
theorem arcAt_2048_Ex : (arcAt 2048).Ex = Rk 2 := by decide
theorem arcAt_2048_Ey : (arcAt 2048).Ey = 0 := by decide

theorem Ec_zero (k : ℕ) (hk : k ≤ 2) : Ec k 0 = (Rk k, 0) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp [Ec, arcAt_0_Ex, arcAt_0_Ey]
  · simp [Ec, arcAt_1024_Ex, arcAt_1024_Ey]
  · simp [Ec, arcAt_2048_Ex, arcAt_2048_Ey]

theorem Ec_1024 (k : ℕ) : Ec k 1024 = (Rk k, 0) := by
  simp [Ec]

theorem conj2_part2 (k j : ℕ) (hk : k ≤ 2) (hj : j < 1024) :
    (match LSc k j with
      | [] => false
      | l :: _ => decide (l.Ax = (Ec k j).1) && decide (l.Ay = (Ec k j).2)) = true ∧
    chainOK (Ec k (j + 1)).1 (Ec k (j + 1)).2 (LSc k j) = true ∧
    gridStep2 (Ec k j).1 (Ec k j).2 (Ec k (j + 1)).1 (Ec k (j + 1)).2 = true ∧
    (LSc k j).all (fun l => decide (l.k = k) && decide (l.G ≤ Gc k j) && leafOK l) = true := by
  have hOK : arcOK2 (arcAt (1024 * k + j)) (Ec k (j + 1)).1 (Ec k (j + 1)).2 = true := by
    by_cases hj' : j + 1 < 1024
    · have h := CJ2v.arcOK2_within arcAt arcAt_linkStep2 arcAt_k k j hk hj'
      have hidx : 1024 * k + j + 1 = 1024 * k + (j + 1) := by omega
      rw [hidx] at h
      have he : Ec k (j + 1) = ((arcAt (1024 * k + (j + 1))).Ex, (arcAt (1024 * k + (j+1))).Ey) := by
        simp [Ec, hj']
      rw [he]
      exact h
    · have hj1023 : j = 1023 := by omega
      subst hj1023
      have h := CJ2v.arcOK2_end arcAt arcAt_linkStep2 arcAt_k arcAt_lastOK k hk
      have he : Ec k (1023 + 1) = (Rk k, 0) := by simp [Ec]
      rw [he]
      exact h
  obtain ⟨hA1, hA2, hA3, hA4⟩ := CJ2v.arcOK2_facts _ _ _ hOK
  have hkk : (arcAt (1024 * k + j)).k = k := by
    have h1 := arcAt_k (1024 * k + j) (by omega)
    omega
  have hEx : (Ec k j).1 = (arcAt (1024 * k + j)).Ex := by simp [Ec, hj]
  have hEy : (Ec k j).2 = (arcAt (1024 * k + j)).Ey := by simp [Ec, hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [LSc]
    rw [hEx, hEy]
    exact hA1
  · simp only [LSc]
    exact hA2
  · rw [hEx, hEy]
    exact hA3
  · simp only [LSc, Gc]
    rw [hkk] at hA4
    exact hA4

/-! ## the weighted maximum sum -/

/-- the maximum log bound of the arc at flat index `i`. -/
def zg (i : ℕ) : ℤ := (arcAt i).Gmax

theorem sum_flat :
    (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024, ∑ j' ∈ Finset.range 1024,
        wtS k * wtS k' * max (Gc k j) (Gc k' j'))
      = ∑ a ∈ Finset.range 3072, ∑ b ∈ Finset.range 3072,
        wtS (a / 1024) * wtS (b / 1024) * max (zg a) (zg b) := by
  have h := CJ2Grid.sum_grid_reindex 3 1024 wtS zg (by norm_num)
  simpa [Gc, zg] using h

theorem vals_get (i : ℕ) (hi : i < Final.vals.length) :
    Final.vals.get ⟨i, hi⟩ = ((arcAt i).Gmax, Final.wt (arcAt i).k) := by
  have hlen : Final.vals.length = Final.arcsAll.length := by simp [Final.vals]
  have hi' : i < Final.arcsAll.length := by omega
  show (Final.arcsAll.map (fun a => (a.Gmax, Final.wt a.k))).get ⟨i, hi⟩
      = ((Final.arcsAll.getD i dummyArc).Gmax, Final.wt (Final.arcsAll.getD i dummyArc).k)
  rw [List.get_eq_getElem, List.getElem_map,
    List.getD_eq_getElem Final.arcsAll dummyArc (n := i) (hn := hi')]

theorem sum_eq_DsumFin :
    (∑ a ∈ Finset.range 3072, ∑ b ∈ Finset.range 3072,
        wtS (a / 1024) * wtS (b / 1024) * max (zg a) (zg b))
      = CJ2.DsumFin Final.vals := by
  have hlen : (3072 : ℕ) = Final.vals.length := by rw [Final.vals_length]
  rw [hlen]
  exact CJ2.sum_range_eq_DsumFin Final.vals (fun a => wtS (a / 1024)) zg
    (fun i hi => by
      simpa [zg] using congrArg Prod.fst (vals_get i hi))
    (fun i hi => by
      have hk : (arcAt i).k = i / 1024 := arcAt_k i (by omega)
      simpa [hk, Final.wt, wtS] using congrArg Prod.snd (vals_get i hi))

theorem merge_bridge : ∀ (f : ℕ) (xs ys : List (ℤ × ℤ)),
    CJ2.merge f xs ys = Final.merge f xs ys := by
  intro f
  induction f with
  | zero => intro xs ys; simp only [CJ2.merge, Final.merge]
  | succ f ih =>
    intro xs ys
    cases xs with
    | nil => simp only [CJ2.merge, Final.merge]
    | cons x xt =>
      cases ys with
      | nil => simp only [CJ2.merge, Final.merge]
      | cons y yt => simp only [CJ2.merge, Final.merge, ih]

theorem msort_bridge : ∀ (f : ℕ) (l : List (ℤ × ℤ)), CJ2.msort f l = Final.msort f l := by
  intro f
  induction f with
  | zero => intro l; simp only [CJ2.msort, Final.msort]
  | succ f ih =>
    intro l
    cases l with
    | nil => simp only [CJ2.msort, Final.msort]
    | cons x t =>
      cases t with
      | nil => simp only [CJ2.msort, Final.msort]
      | cons y t' => simp only [CJ2.msort, Final.msort, ih, merge_bridge]

theorem sortedSum_bridge : ∀ (l : List (ℤ × ℤ)) (c acc : ℤ),
    CJ2.sortedSum l c acc = Final.sortedSum l c acc := by
  intro l
  induction l with
  | nil => intro c acc; simp only [CJ2.sortedSum, Final.sortedSum]
  | cons x t ih =>
    intro c acc
    obtain ⟨v, w⟩ := x
    simp only [CJ2.sortedSum, Final.sortedSum, ih]

theorem conj2_sum :
    (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024, ∑ j' ∈ Finset.range 1024,
        wtS k * wtS k' * max (Gc k j) (Gc k' j')) ≤ 112 * DENS2 * DENS2 * S / 10 := by
  rw [sum_flat, sum_eq_DsumFin, CJ2Sum.DsumFin_eq_Dsum]
  rw [CJ2Sum.Dsum_perm Final.vals (CJ2.msort 20 Final.vals) (CJ2Sum.msort_perm 20 Final.vals)]
  have h20 : Final.vals.length ≤ 2 ^ 20 := by rw [Final.vals_length]; norm_num
  have hs := CJ2Sum.sortedSum_eq_Dsum (CJ2.msort 20 Final.vals) 0 0
    (CJ2Sum.msort_sorted 20 Final.vals h20)
  have hs' : CJ2.sortedSum (CJ2.msort 20 Final.vals) 0 0 = CJ2.Dsum (CJ2.msort 20 Final.vals) := by
    simpa using hs
  rw [← hs']
  have hbridge : CJ2.sortedSum (CJ2.msort 20 Final.vals) 0 0
      = Final.sortedSum (Final.msort 20 Final.vals) 0 0 := by
    rw [msort_bridge 20 Final.vals, sortedSum_bridge]
  rw [hbridge]
  simpa [Final.total, Final.DEN, DENS2] using Final.total_ok

/-! ## assembly -/

theorem conj2_cert2 : Conj2Cert2 := by
  refine ⟨Gc, Ec, LSc, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨Ec_zero k hk, Ec_1024 k⟩
  · intro k j hk hj
    exact conj2_part2 k j hk hj
  · exact conj2_sum


end Work.Cert
