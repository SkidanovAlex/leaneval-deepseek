/-
# AREA COPR — deliverables

Assembly of the six `Prop`s of area COPR from their component results:

* `Work.GW2.coprime11i`  ← `Work.COPR.coprime11i_iterated`, `Work.COPR.coprime11i_split`
* `Work.GW2.coprime11ii` ← `Work.COPR.coprime11ii_exists`, `Work.COPR.coprime11ii_conj`
* `Work.GW2.coprime11iii`← `Work.COPR.coprime11iii`
* `Work.GW2.coprime11iv` ← `Work.COPR.coprime11iv`
* `Work.GW2.coprime13`   ← `Work.COPR.coprime13`
* `Work.GW2.coprime15`   ← `Work.COPR.coprime15_gen`, `Work.COPR.coprime15_sub`

and the bundle `Work.GW2.CoprimeArea` collecting them.
-/
import Submission.Work.COPR.Coprime11i
import Submission.Work.COPR.coprime11ii_exists
import Submission.Work.COPR.coprime11ii_conj
import Submission.Work.COPR.coprime11iii
import Submission.Work.COPR.coprime11iv
import Submission.Work.COPR.coprime13
import Submission.Work.COPR.coprime15_gen
import Submission.Work.COPR.coprime15_sub

namespace Work.GW2

/-- Bender 1981, 1.1(i): `[P,[P,K]] = [P,K]` and `K = [P,K]·C_K(P)` for a `p`-group `P` acting
coprimely on a `p'`-group `K`. -/
theorem coprime11i : Coprime11iProp := fun _ _ _ p _ P K hP hcop hN =>
  ⟨Work.COPR.coprime11i_iterated p P K hP hcop hN, Work.COPR.coprime11i_split p P K hP hcop hN⟩

/-- Bender 1981, 1.1(ii): existence and `C_K(P)`-conjugacy of `P`-invariant Sylow `q`-subgroups. -/
theorem coprime11ii : Coprime11iiProp := by
  intro G _ _ p _ P K hP hcop hN q _ Q hQK hQq hNQ
  exact ⟨Work.COPR.coprime11ii_exists (G := G) (p := p) (P := P) (K := K) hP hcop hN q Q hQK hQq hNQ,
    Work.COPR.coprime11ii_conj (G := G) (p := p) (P := P) (K := K) hP hcop hN q⟩

/-- Bender 1981, 1.1(iii): `K = ⨆_{a ∈ E#} C_K(a)` for `E ≤ P` elementary abelian of order `p²`. -/
theorem coprime11iii : Coprime11iiiProp := Work.COPR.coprime11iii

/-- Bender 1981, 1.1(iv). -/
theorem coprime11iv : Coprime11ivProp := Work.COPR.coprime11iv

/-- Bender 1981, 1.3. -/
theorem coprime13 : Coprime13Prop := Work.COPR.coprime13

/-- Bender 1981, 1.5. -/
theorem coprime15 : Coprime15Prop := by
  intro G _ _ hFT X s hs hodd hN
  refine ⟨?_, ?_, ?_⟩
  · exact (Work.COPR.coprime15_gen (G := G) (X := X) (s := s) hs hodd hN).1
  · exact (Work.COPR.coprime15_gen (G := G) (X := X) (s := s) hs hodd hN).2
  · exact Work.COPR.coprime15_sub (G := G) (X := X) (s := s) hs hodd hN

/-- The six COPR deliverable `Prop`s bundled together, for convenient filling of the areas'
`LocalToolkit`. -/
structure CoprimeArea : Prop where
  c11i : Coprime11iProp
  c11ii : Coprime11iiProp
  c11iii : Coprime11iiiProp
  c11iv : Coprime11ivProp
  c13 : Coprime13Prop
  c15 : Coprime15Prop

/-- All six COPR deliverables. -/
theorem coprimeArea : CoprimeArea :=
  ⟨coprime11i, coprime11ii, coprime11iii, coprime11iv, coprime13, coprime15⟩

end Work.GW2
