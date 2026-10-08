import Mathlib
import Submission.Work.NormalComplement.Sections

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## Auxiliary facts used in the assembly -/

/-- **Step 1 of Theorem D**: a strongly embedded subgroup that is not the whole group has an
involution outside it.  Conjugation of an involution `u ∈ H` by an element `g ∉ H` produces `t`
with `t ∉ H`, because otherwise `u` would lie in `H ⊓ conj g⁻¹ H`, making that intersection even,
while strong embedding of `H` makes it odd. -/
theorem exists_involution_not_mem (G : Type) [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) : ∃ t : G, orderOf t = 2 ∧ t ∉ H := by
  have hne : H ≠ ⊤ := hH.1
  have hg : ∃ g : G, g ∉ H := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨g, hgH⟩ := hg
  have heven : 2 ∣ Nat.card H := even_iff_two_dvd.mp hH.2.1
  obtain ⟨u, huH, hu2⟩ : ∃ u ∈ H, orderOf u = 2 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 heven
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  refine ⟨MulAut.conj g u, ?_, ?_⟩
  · rw [MulAut.conj_apply]
    exact (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm.trans hu2
  · intro ht
    have hgHinv : g⁻¹ ∉ H := fun h => hgH (by simpa using H.inv_mem h)
    have hmem : u ∈ H ⊓ conj g⁻¹ H := by
      refine ⟨huH, ?_⟩
      exact Subgroup.mem_map.mpr ⟨MulAut.conj g u, ht, by
        change (MulAut.conj g⁻¹) (MulAut.conj g u) = u
        rw [MulAut.conj_apply, MulAut.conj_apply]; group⟩
    have hdvd : 2 ∣ Nat.card (H ⊓ conj g⁻¹ H : Subgroup G) := by
      have hz : Subgroup.zpowers u ≤ H ⊓ conj g⁻¹ H := Subgroup.zpowers_le.mpr hmem
      have := Subgroup.card_dvd_of_le hz
      rwa [Nat.card_zpowers, hu2] at this
    exact (Nat.not_even_iff_odd.mpr (hH.2.2 g⁻¹ hgHinv)) (even_iff_two_dvd.mpr hdvd)

/-- A nontrivial solvable group is not perfect: its commutator subgroup is strictly smaller. -/
theorem commutator_lt_of_isSolvable {G : Type*} [Group G] {E : Subgroup G} (hEne : E ≠ ⊥)
    (hEsol : Group.IsSolvable ↥E) : ⁅E, E⁆ < E := by
  rw [lt_iff_le_and_ne]
  refine ⟨Subgroup.commutator_le_self E, ?_⟩
  intro hEq
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).mpr hEne
  haveI : Group.IsPerfect ↥E := (Subgroup.isPerfect_iff).mpr hEq
  exact Group.IsPerfect.not_isSolvable ↥E hEsol

/-- **Theorem D assembled from the interface of `Sections.lean`.**

Proof outline (Peterfalvi I Ch. III §1–§2, pp. 172–176; `REFS/peterfalvi_I_ch3_4.md`):
1. *An involution outside `H`.* `hH.1 : H ≠ ⊤` gives `g ∉ H`; `hH.2.1 : Even (Nat.card H)` gives
   (Cauchy, `exists_prime_orderOf_dvd_card'`) an involution `u ∈ H`.  Then `t := MulAut.conj g u` has
   `orderOf t = 2` and `t ∉ H`: otherwise `u ∈ H ⊓ conj g⁻¹ H` makes that intersection even, while
   `hH.2.2 g⁻¹ hg⁻¹` makes it odd.
2. *The minimal counterexample.* `D := twoPoint H t = H ⊓ conj t H` has odd order (`hH.2.2 t htH`).
   Among all `W` with `W ≤ H`, `H ≤ N_G(W)`, `W ⊔ D = H` (nonempty: `W = H`) choose one of minimal
   `Nat.card` (e.g. `Nat.find` on `∃ W ∈ S, Nat.card W = k`).
3. *`W ⊓ D = ⊥`.* Put `E := W ⊓ D` and suppose `E ≠ ⊥`.  `|E|` is odd (`Subgroup.card_dvd_of_le`
   from `Odd |D|`), so `E` is solvable by `hFT`.  Let `q` be any prime with `q ∣ [E : E']`
   (`E' ≠ E` because `E ≠ ⊥` is solvable); `hPab` gives a `q`-element `y ∈ E ∖ E'`.
   `hS2` gives `E` `q`-control in `W`, or the `q`-Sylow datum.
   * If `E` were `q`-control for some `q`, `hTrans` gives `y ∉ O^q(W)` and `hStrat` produces
     `W₁ < W` with `W₁ ≤ H`, `H ≤ N_G(W₁)`, `W₁ ⊔ D = H` — contradicting minimality of `W`.
   * Otherwise the Sylow datum holds for every prime `q ∣ [E:E']`, i.e. `IsD1 H t W`, and `hN`
     applies (this is §3–§5).
4. *Conclusion.* `Q := W`: `Q ≤ H`, `H ≤ N_G(Q)`, `Q ⊓ D = ⊥`, `Q ⊔ D = H`.

Available API: `Work.ThreePoints.Omega` (`exists_conj_mem`, `card_inf_conj_odd`), the workspace
lemmas `Subgroup.card_dvd_of_le`, `Subgroup.relIndex_mul_card`-style index facts, and
`Nat.find`/`Nat.find_spec`/`Nat.find_min'` for the minimal `W`. -/
theorem thmD_of_sections (hFT : Submission.Blueprint.FeitThompsonProp)
    (hTrans : Work.NormalComplement.TransferProp) (hStrat : Work.NormalComplement.StrategyProp)
    (hPab : Work.NormalComplement.PrimesOfAbelianizationProp)
    (hX : Work.NormalComplement.AppXProp) (hS2 : Work.NormalComplement.Section2Prop) (hN : Work.NormalComplement.NoD1Prop) :
    Submission.Blueprint.ThmDProp := by
  classical
  intro G _ _ hSit H hH
  -- Step 1: an involution `t ∉ H`.
  obtain ⟨t, ht2, htH⟩ := exists_involution_not_mem G hH
  -- Step 2: `D = twoPoint H t` has odd order.
  have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
  -- The family of admissible subgroups, and a minimal member.
  let S : Set (Subgroup G) :=
    {W | W ≤ H ∧ H ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ twoPoint H t = H}
  have hSH : H ∈ S := ⟨le_rfl, Subgroup.le_normalizer, by rw [sup_eq_left]; exact inf_le_left⟩
  have hex : ∃ k : ℕ, ∃ W : Subgroup G, W ∈ S ∧ Nat.card W = k := ⟨_, H, hSH, rfl⟩
  obtain ⟨W, hWS, hWval⟩ : ∃ W : Subgroup G, W ∈ S ∧ Nat.card W = Nat.find hex :=
    Nat.find_spec hex
  have hWmin : ∀ W' ∈ S, Nat.card W ≤ Nat.card W' := by
    intro W' hW'
    rw [hWval]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  -- Step 3: `W ⊓ D = ⊥`.
  have hWinf : W ⊓ twoPoint H t = ⊥ := by
    by_contra hWD
    let E : Subgroup G := W ⊓ twoPoint H t
    have hEne : E ≠ ⊥ := hWD
    have hEodd : Odd (Nat.card ↥E) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le (show E ≤ twoPoint H t from inf_le_right))
    have hEsol : Group.IsSolvable ↥E := hFT ↥E hEodd
    have hElt : ⁅E, E⁆ < E := commutator_lt_of_isSolvable hEne hEsol
    have hIsD1 : IsD1 H t W := by
      intro p hp hpdvd
      haveI : Fact p.Prime := ⟨hp⟩
      have hpcard : p ∣ Nat.card ↥(W ⊓ twoPoint H t) :=
        dvd_trans hpdvd
          (Subgroup.relIndex_dvd_card ⁅W ⊓ twoPoint H t, W ⊓ twoPoint H t⁆
            (W ⊓ twoPoint H t))
      rcases hS2 G hSit H hH t ht2 htH W hWS.1 hWS.2.1 hWS.2.2 (hX G hSit H hH t ht2 htH) p hp hpcard with hA | hB
      · exfalso
        obtain ⟨y, hyE, hyE', hyord⟩ := hPab G E hEne hEsol p hp hpdvd
        have hy1 : y ≠ 1 := by
          rintro rfl
          exact hyE' (Subgroup.one_mem _)
        have hyW : y ∈ W := hA.1 hyE
        have hyres : y ∉ Work.Grun.pResidual p W := hTrans G hA hyE hy1 hyord hyE' hpdvd
        obtain ⟨W₁, hlt, hW₁H, hHn₁, hW₁D⟩ :=
          hStrat G hA.1 inf_le_right hA.2.1 hWS.1 hWS.2.1 hWS.2.2 hyW hyres
        exact (not_lt.mpr (hWmin W₁ ⟨hW₁H, hHn₁, hW₁D⟩)) (Subgroup.card_lt_of_lt hlt)
      · exact hB
    exact hN G hSit H hH t ht2 htH W hWS.1 hWS.2.1 hWS.2.2 hWD hIsD1
  -- Step 4: `Q := W` is the normal complement.
  exact ⟨t, ht2, htH, W, hWS.1, hWS.2.1, hWinf, hWS.2.2⟩

end Work.NormalComplement
