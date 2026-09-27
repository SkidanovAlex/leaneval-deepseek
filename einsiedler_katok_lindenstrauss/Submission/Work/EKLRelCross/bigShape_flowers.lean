import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.free_orbits_of_contracting
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLRelCross.pisa_crosssection
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.flower_size_facts_gen
import Submission.Work.EKLRelCross.Ucl_inv_subset_V

/-!
# `Work.EKLRelCross.bigShape_flowers`

Flowers of `U`-plaques exist (Pisa 6.13–6.15): for a horospherical `U ≤ SL₃(ℝ)`, a probability
measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by `α^{t₀}` and contracting `U`, and any `R > 0`,
there are countably many plaque algebras `(Z n, m n)` with Borel bases `G n ⊆ Z n` whose union is
conull and at whose points the whole `R`-plaque of the point lies in the atom of the plaque
algebra.

## Route

* `Work.EKLRelCross.free_orbits_of_contracting` gives a.e. freeness of the `U`-orbits; the free
  set `Fr` is Borel (`freeSet_borel`) and conull.
* `Work.EKLRelCross.pisa_crosssection` (Pisa 6.7 + 6.9–6.12) gives, through every free point `x₀`
  and at any scale, a *bounded* `U`-cross-section: an open `E ∋ x₀` and a Borel `C` such that
  every `y ∈ E` is `y = t⁻¹ • (t • y)` with the *return map* `t` in the closed unit ball
  `Ucl U 1` and `t • y ∈ C`, and such that `C` meets each `U`-orbit at most once inside the closed
  ball `Ucl U ρ`, `ρ` as large as we like.
* The covering scale is therefore `c₀ = 2(1+1)² + 2`, since `(Ucl U 1)⁻¹ ⊆ V c₀`
  (`Work.EKLRelCross.Ucl_inv_subset_V`).
* `Work.EKLRelCross.flower_size_facts_gen` chooses `δ, b > 0` with `c₀ ≤ δ`,
  `V R · V c₀ ⊆ V δ`, `(Vinv δ ∩ U)(V δ ∩ U) ⊆ V b` and `(V δ ∩ U)⁻¹(V δ ∩ U) ⊆ V b`.
* `atom_flower_local` computes the atom of the flower σ-algebra `flowerSigma U δ C W` at a plaque
  point as the plaque `(V δ ∩ U) • z`, and `flower_plaqueAlgebra_bdd` shows that the flower is a
  plaque algebra with `Z = ⋃_{c ∈ C ∩ Fr} [c]`.
* A fixed countable basis `O` of `X₃` (padded with `univ` to give `W`, `W 0 = univ`) yields, for
  every free point, one index `k` with `O k` contained in its cross-section neighbourhood; the
  corresponding pairs `(Z k, m k, G k = E k ∩ Fr)` cover `Fr` up to a null set.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- Monotonicity of the displacement boxes. -/
lemma bigShape_V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

theorem bigShape_flowers (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z G : ℕ → Set Work.EKLContract.X3) (m : ℕ → MeasurableSpace Work.EKLContract.X3),
      (∀ n, Work.EKLContract.IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      μ (⋃ n, G n)ᶜ = 0 ∧
      (∀ n, ∀ x ∈ G n, ∀ u ∈ (Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)), u • x ∈ Work.EKLContract.atom (m n) x) := by
  classical
  have hfree_ae : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    free_orbits_of_contracting h2 hU t0 ht0 hcontr
  haveI : SecondCountableTopology X3 := secondCountableTopology_X3 h2
  set c₀ : ℝ := 2 * (1 + 1) ^ 2 + 2 with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; norm_num
  have hc₀inv : ∀ g ∈ Ucl U 1, g⁻¹ ∈ V c₀ := by
    intro g hg
    rw [hc₀def]
    exact Ucl_inv_subset_V (U := U) (a := 1) (by norm_num) hg
  obtain ⟨δ, b, hδ, hb, hc₀δ, hsize1, hprod, hprod2⟩ :=
    flower_size_facts_gen (U := U) (R := R) hR (c₀ := c₀) hc₀pos
  set Fr : Set X3 := {x : X3 | ∀ u ∈ U, u • x = x → u = 1} with hFrdef
  have hFrmeas : MeasurableSet Fr := freeSet_borel hU.1
  have hFraec : μ Frᶜ = 0 := by
    have h := MeasureTheory.ae_iff.mp hfree_ae
    have hset : Frᶜ = {a : X3 | ¬ (∀ u ∈ U, u • a = a → u = 1)} := by
      rw [hFrdef]
      ext a
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [hset]
    exact h
  obtain ⟨O, hObas⟩ := TopologicalSpace.exists_seq_basis X3
  set W : ℕ → Set X3 := (fun n => if n = 0 then Set.univ else O (n - 1)) with hWdef
  have hW0 : W 0 = Set.univ := by simp [hWdef]
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [hW0]; exact isOpen_univ
    · simp only [hWdef, hn, if_false]
      exact hObas.isOpen (Set.mem_range_self (n - 1))
  have hWgen : borel X3 = MeasurableSpace.generateFrom (Set.range W) := by
    have hle1 : MeasurableSpace.generateFrom (Set.range O) ≤
        MeasurableSpace.generateFrom (Set.range W) :=
      MeasurableSpace.generateFrom_mono (by
        rintro s ⟨k, rfl⟩
        exact ⟨k + 1, by simp [hWdef]⟩)
    have hle2 : MeasurableSpace.generateFrom (Set.range W) ≤
        MeasurableSpace.generateFrom (Set.range O) := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨n, rfl⟩
      by_cases hn : n = 0
      · rw [show W n = Set.univ by simp only [hWdef, hn, if_true]]
        exact MeasurableSet.univ
      · simp only [hWdef, hn, if_false]
        exact MeasurableSpace.measurableSet_generateFrom ⟨n - 1, rfl⟩
    rw [hObas.borel_eq_generateFrom]
    exact le_antisymm hle1 hle2
  have hsep_all : ∀ z z' : X3, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z' := by
    intro z z' hpat
    by_contra hne
    obtain ⟨u, v, hu, hv, hzu, hz'v, hdisj⟩ := t2_separation hne
    obtain ⟨t, ht, hzt, htu⟩ := (hObas.isOpen_iff.mp hu) z hzu
    obtain ⟨m, rfl⟩ := ht
    have h1 : z ∈ W (m + 1) := by
      simp only [hWdef, Nat.succ_ne_zero, if_false]
      exact hzt
    have h2 : z' ∉ W (m + 1) := by
      simp only [hWdef, Nat.succ_ne_zero, if_false]
      intro hmem
      exact (Set.disjoint_left.mp hdisj (htu hmem)) hz'v
    exact h2 ((hpat (m + 1)).mp h1)
  have hXsec : ∀ x : X3, (∀ u ∈ U, u • x = x → u = 1) →
      ∃ (E C : Set X3), IsOpen E ∧ x ∈ E ∧ MeasurableSet C ∧
        (∀ y ∈ E, ∃ z ∈ C, ∃ u ∈ U, u ∈ V c₀ ∧ u • z = y) ∧
        (∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1) := by
    intro x₀ hxfree
    have hinj : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂ heq
      have hfix : (u₂⁻¹ * u₁) • x₀ = x₀ := by rw [mul_smul, heq, inv_smul_smul]
      have h1 : u₂⁻¹ * u₁ = 1 := hxfree _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
      calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
        _ = u₂ := by rw [h1, mul_one]
    obtain ⟨E, C, -, hEint, -, hCmeas, huniq, hCS⟩ :=
      pisa_crosssection hU.1 x₀ (ρ := b + 3) (by linarith) hinj
    refine ⟨interior E, C, isOpen_interior, hEint, hCmeas, ?_, ?_⟩
    · intro y hy
      obtain ⟨t, ht, -⟩ := huniq y (interior_subset hy)
      exact ⟨t • y, ht.2, t⁻¹, U.inv_mem ht.1.1, hc₀inv t ht.1, by rw [inv_smul_smul]⟩
    · intro z hz u huU huV hzu
      exact hCS z hz u ⟨huU, fun i j => le_of_lt (lt_of_lt_of_le (huV i j) (by linarith))⟩ hzu
  have hdata' : ∀ x : X3, (∀ u ∈ U, u • x = x → u = 1) →
      ∃ (d : Set X3 × Set X3), IsOpen d.1 ∧ x ∈ d.1 ∧ MeasurableSet d.2 ∧
        (∀ y ∈ d.1, ∃ z ∈ d.2, ∃ u ∈ U, u ∈ V c₀ ∧ u • z = y) ∧
        (∀ z ∈ d.2, ∀ u ∈ U, u ∈ V b → u • z ∈ d.2 → u = 1) := by
    intro x hx
    obtain ⟨E, C, h1, h2', h3, h4, h5⟩ := hXsec x hx
    exact ⟨(E, C), h1, h2', h3, h4, h5⟩
  let data : X3 → Set X3 × Set X3 := fun x =>
    if h : (∀ u ∈ U, u • x = x → u = 1) then Classical.choose (hdata' x h) else (∅, ∅)
  have hdataprop : ∀ x (hx : ∀ u ∈ U, u • x = x → u = 1),
      IsOpen (data x).1 ∧ x ∈ (data x).1 ∧ MeasurableSet (data x).2 ∧
      (∀ y ∈ (data x).1, ∃ z ∈ (data x).2, ∃ u ∈ U, u ∈ V c₀ ∧ u • z = y) ∧
      (∀ z ∈ (data x).2, ∀ u ∈ U, u ∈ V b → u • z ∈ (data x).2 → u = 1) := by
    intro x hx
    have h : data x = Classical.choose (hdata' x hx) := by
      simp only [data]
      exact dif_pos hx
    rw [h]
    exact Classical.choose_spec (hdata' x hx)
  let M : ℕ → Prop := fun n => ∃ y : X3, (∀ u ∈ U, u • y = y → u = 1) ∧ O n ⊆ (data y).1
  let P : ℕ → Set X3 × Set X3 := fun n =>
    if h : M n then data (Classical.choose h) else (∅, ∅)
  have hPprop : ∀ n, IsOpen (P n).1 ∧ MeasurableSet (P n).2 ∧
      (∀ y ∈ (P n).1, ∃ z ∈ (P n).2, ∃ u ∈ U, u ∈ V c₀ ∧ u • z = y) ∧
      (∀ z ∈ (P n).2, ∀ u ∈ U, u ∈ V b → u • z ∈ (P n).2 → u = 1) := by
    intro n
    by_cases hM : M n
    · have h : P n = data (Classical.choose hM) := by simp only [P]; exact dif_pos hM
      rw [h]
      obtain ⟨hy, -⟩ := Classical.choose_spec hM
      obtain ⟨h1, h2', h3, h4, h5⟩ := hdataprop (Classical.choose hM) hy
      exact ⟨h1, h3, h4, h5⟩
    · have h : P n = (∅, ∅) := by simp only [P]; exact dif_neg hM
      rw [h]
      exact ⟨isOpen_empty, MeasurableSet.empty, by simp, by simp⟩
  let Z : ℕ → Set X3 := fun n => ⋃ c ∈ (P n).2 ∩ Fr, atom (flowerSigma U δ (P n).2 W) c
  let m : ℕ → MeasurableSpace X3 := fun n => flowerSigma U δ (P n).2 W
  let G : ℕ → Set X3 := fun n => (P n).1 ∩ Fr
  refine ⟨Z, G, m, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hopen, hmeas, hcov, hcs⟩ := hPprop n
    show IsPlaqueAlgebra U (⋃ c ∈ (P n).2 ∩ Fr, atom (flowerSigma U δ (P n).2 W) c)
      (flowerSigma U δ (P n).2 W)
    exact flower_plaqueAlgebra_bdd h2 hU.1 hmeas hcs hδ hprod hprod2 hW0 hWopen hWgen
      (fun z _ z' _ hpat => hsep_all z z' hpat)
  · intro n
    obtain ⟨hopen, hmeas, hcov, hcs⟩ := hPprop n
    refine ⟨hopen.measurableSet.inter hFrmeas, ?_⟩
    intro y hy
    obtain ⟨hyE, hyFr⟩ := hy
    obtain ⟨z, hz, u₀, hu₀U, hu₀V, hu₀z⟩ := hcov y hyE
    have hzFr : z ∈ Fr := by
      rw [hFrdef]
      intro u' hu' hu'z
      have hfix : (u₀ * u' * u₀⁻¹) • y = y := by
        have h1 : u₀⁻¹ • y = z := by rw [← hu₀z, inv_smul_smul]
        calc (u₀ * u' * u₀⁻¹) • y = u₀ • (u' • (u₀⁻¹ • y)) := by rw [mul_smul, mul_smul]
          _ = u₀ • (u' • z) := by rw [h1]
          _ = u₀ • z := by rw [hu'z]
          _ = y := hu₀z
      have h1 : u₀ * u' * u₀⁻¹ = 1 :=
        hyFr _ (U.mul_mem (U.mul_mem hu₀U hu') (U.inv_mem hu₀U)) hfix
      calc u' = u₀⁻¹ * (u₀ * u' * u₀⁻¹) * u₀ := by group
        _ = 1 := by rw [h1]; group
    show y ∈ ⋃ c ∈ (P n).2 ∩ Fr, atom (flowerSigma U δ (P n).2 W) c
    refine Set.mem_iUnion₂.mpr ⟨z, ⟨hz, hzFr⟩, ?_⟩
    have h1Vδ : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδ).2
    have hatom : atom (flowerSigma U δ (P n).2 W) z
        = (fun u : SL3 => u • z) '' (V δ ∩ (U : Set SL3)) :=
      atom_flower_local (U := U) (C := (P n).2) (b := b) hcs (δ := δ) hδ hprod
        (W := W) hW0 (fun z _ z' _ hpat => hsep_all z z' hpat) (v := 1) h1Vδ U.one_mem
        (z := z) hz (x := z) (by rw [one_smul])
    rw [hatom]
    exact ⟨u₀, ⟨bigShape_V_mono hc₀δ hu₀V, hu₀U⟩, hu₀z⟩
  · have hsub : (⋃ n, G n)ᶜ ⊆ Frᶜ := by
      intro y hy
      rw [Set.mem_compl_iff]
      intro hyFr
      obtain ⟨hopen, hmem, hmeas, hcov, hcs⟩ := hdataprop y hyFr
      obtain ⟨t, ht, hyt, htu⟩ := (hObas.isOpen_iff.mp hopen) y hmem
      obtain ⟨k, rfl⟩ := ht
      have hMk : M k := ⟨y, hyFr, htu⟩
      have hPk : P k = data (Classical.choose hMk) := by simp only [P]; exact dif_pos hMk
      have hspec := Classical.choose_spec hMk
      have hyG : y ∈ G k := by
        show y ∈ (P k).1 ∩ Fr
        refine ⟨?_, hyFr⟩
        rw [hPk]
        exact hspec.2 hyt
      exact hy (Set.mem_iUnion.mpr ⟨k, hyG⟩)
    exact measure_mono_null hsub hFraec
  · intro n x hx u hu
    obtain ⟨hopen, hmeas, hcov, hcs⟩ := hPprop n
    obtain ⟨hxE, hxFr⟩ := hx
    obtain ⟨z, hz, u₀, hu₀U, hu₀V, hu₀z⟩ := hcov x hxE
    have hatom : atom (flowerSigma U δ (P n).2 W) x
        = (fun u : SL3 => u • z) '' (V δ ∩ (U : Set SL3)) :=
      atom_flower_local (U := U) (C := (P n).2) (b := b) hcs (δ := δ) hδ hprod
        (W := W) hW0 (fun z _ z' _ hpat => hsep_all z z' hpat) (v := u₀)
        (bigShape_V_mono hc₀δ hu₀V) hu₀U (z := z) hz hu₀z.symm
    show u • x ∈ atom (flowerSigma U δ (P n).2 W) x
    rw [hatom]
    exact ⟨u * u₀, ⟨hsize1 u hu.1 u₀ hu₀V, U.mul_mem hu.2 hu₀U⟩,
      by show (u * u₀) • z = u • x; rw [mul_smul, hu₀z]⟩

end Work.EKLRelCross
