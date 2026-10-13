import Mathlib
import Submission.Work.WilE4.CAD.disk_roots_card_eventually_const
import Submission.Work.WilE4.CAD.multiset_card_eq_sum_filter_of_disjoint
import Submission.Work.WilE4.CAD.rootMultiplicity_gcd_complex
import Submission.Work.WilE4.CAD.roots_filter_card_eq_rootMultiplicity

set_option maxHeartbeats 1000000

noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open Polynomial

/-! ## A finite set of positive reals has a positive lower bound -/

lemma exists_pos_lt_of_finset : ∀ (C : Finset ℝ), (∀ r ∈ C, 0 < r) →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r ∈ C, ρ < r := by
  intro C
  induction C using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, one_pos, fun r hr => absurd hr (Finset.notMem_empty r)⟩
  | insert a s _ha ih =>
      intro hC
      have hapos : 0 < a := hC a (Finset.mem_insert_self a s)
      have hspos : ∀ r ∈ s, 0 < r := fun r hr => hC r (Finset.mem_insert_of_mem hr)
      obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := ih hspos
      refine ⟨min ρ₀ (a / 2), lt_min hρ₀pos (by linarith), ?_⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hρ₀ r hr)

/-- **The common root near `t₀` persists and is unique.**

Let `F`, `G` be families of complex polynomials whose coefficients depend continuously on the
parameter, of degree bounded by `d`, and let `x : ℕ → (Fin m → ℝ)` tend to `x₀`, with `F x₀`, `G x₀`
nonzero.  Assume that

* the number of distinct roots of `F (x n)` (resp. `G (x n)`) equals that of `F x₀` (resp. `G x₀`),
* the degree of `gcd (F (x n)) (G (x n))` equals that of `gcd (F x₀) (G x₀)`,

and that `t₀` is a common root of `F x₀` and `G x₀` which is separated by `δ > 0` from all the other
roots of both.  Then eventually `F (x n)` and `G (x n)` have a common root at distance `< δ` from
`t₀`, and it is the only root of either polynomial in that ball.

The proof compares the two decompositions of the root multiset of the gcd into the disjoint disks of
radius `ρ < δ` around the distinct roots of `F x₀` and `G x₀`: the argument-principle count
`disk_roots_card_eventually_const` pins the multiplicity of every fibre in every disk to the
multiplicity at `x₀`, so the degree of the gcd is a sum of the minima of these multiplicities; the
constant-degree hypothesis for the gcd then forces each single summand — in particular the one at
`t₀` — to attain its maximal value. -/
theorem common_root_unique {m : ℕ} (F G : (Fin m → ℝ) → Polynomial ℂ) (d : ℕ)
    (hcontF : ∀ k, Continuous fun x : Fin m → ℝ => (F x).coeff k)
    (hcontG : ∀ k, Continuous fun x : Fin m → ℝ => (G x).coeff k)
    (hdegF : ∀ x : Fin m → ℝ, (F x).natDegree ≤ d)
    (hdegG : ∀ x : Fin m → ℝ, (G x).natDegree ≤ d)
    (x : ℕ → Fin m → ℝ) {x₀ : Fin m → ℝ} (hx : Filter.Tendsto x Filter.atTop (nhds x₀))
    (hF : F x₀ ≠ 0) (hG : G x₀ ≠ 0)
    (hcardF : ∀ n, (F (x n)).roots.toFinset.card = (F x₀).roots.toFinset.card)
    (hcardG : ∀ n, (G (x n)).roots.toFinset.card = (G x₀).roots.toFinset.card)
    (hgcd : ∀ n, (gcd (F (x n)) (G (x n))).natDegree = (gcd (F x₀) (G x₀)).natDegree)
    {t₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (ht₀F : (F x₀).IsRoot t₀) (ht₀G : (G x₀).IsRoot t₀)
    (hfarF : ∀ z : ℂ, (F x₀).IsRoot z → z ≠ t₀ → δ < dist z t₀)
    (hfarG : ∀ z : ℂ, (G x₀).IsRoot z → z ≠ t₀ → δ < dist z t₀) :
    ∀ᶠ n in Filter.atTop, ∃ z : ℂ, dist z t₀ < δ ∧ (F (x n)).IsRoot z ∧ (G (x n)).IsRoot z ∧
      (∀ w : ℂ, (F (x n)).IsRoot w → dist w t₀ < δ → w = z) ∧
      (∀ w : ℂ, (G (x n)).IsRoot w → dist w t₀ < δ → w = z) := by
  classical
  -- The distinct roots of the two limit polynomials.
  let RF : Finset ℂ := (F x₀).roots.toFinset
  let RG : Finset ℂ := (G x₀).roots.toFinset
  let S : Finset ℂ := RF ∪ RG
  have hmF : ∀ z : ℂ, z ∈ RF ↔ (F x₀).IsRoot z :=
    fun z => Multiset.mem_toFinset.trans (Polynomial.mem_roots hF)
  have hmG : ∀ z : ℂ, z ∈ RG ↔ (G x₀).IsRoot z :=
    fun z => Multiset.mem_toFinset.trans (Polynomial.mem_roots hG)
  have hmS : ∀ z : ℂ, z ∈ S ↔ ((F x₀).IsRoot z ∨ (G x₀).IsRoot z) :=
    fun z => Finset.mem_union.trans (or_congr (hmF z) (hmG z))
  have htF : t₀ ∈ RF := (hmF t₀).mpr ht₀F
  have htG : t₀ ∈ RG := (hmG t₀).mpr ht₀G
  have htS : t₀ ∈ S := Finset.mem_union_left _ htF
  have hfar : ∀ z ∈ S, z ≠ t₀ → δ < dist z t₀ := by
    intro z hz hne
    rcases (hmS z).mp hz with h | h
    · exact hfarF z h hne
    · exact hfarG z h hne
  -- Choose the working radius: below `δ`, half the distances between distinct roots, and a third of
  -- the distance of every other root to `t₀` minus `δ`.
  set PairC : Finset (ℂ × ℂ) := (S.product S).filter (fun p : ℂ × ℂ => p.1 ≠ p.2) with hPairC
  set PtC : Finset ℂ := S.filter (fun z => z ≠ t₀) with hPtC
  set C : Finset ℝ := insert δ (PairC.image (fun p : ℂ × ℂ => dist p.1 p.2 / 2)
        ∪ PtC.image (fun z => (dist z t₀ - δ) / 3)) with hC
  have hCpos : ∀ r ∈ C, 0 < r := by
    intro r hr
    rw [hC] at hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hδ
    · rcases Finset.mem_union.mp hr with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        rw [hPairC] at hp
        obtain ⟨-, hne⟩ := Finset.mem_filter.mp hp
        have h2 := dist_pos.mpr hne
        linarith
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        rw [hPtC] at hz
        obtain ⟨hzS, hne⟩ := Finset.mem_filter.mp hz
        have h2 := hfar z hzS hne
        linarith
  obtain ⟨ρ, hρpos, hρlt⟩ := exists_pos_lt_of_finset C hCpos
  have hρδ : ρ < δ := hρlt δ (by rw [hC]; exact Finset.mem_insert_self δ _)
  have hρpair : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → 2 * ρ < dist z z' := by
    intro z hz z' hz' hne
    have hmem : dist z z' / 2 ∈ C := by
      rw [hC]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(z, z'), by
          rw [hPairC]
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hz'⟩, hne⟩, rfl⟩)))
    have h2 := hρlt _ hmem
    linarith
  have hρfar : ∀ z ∈ S, z ≠ t₀ → δ + 2 * ρ < dist z t₀ := by
    intro z hz hne
    have hmem : (dist z t₀ - δ) / 3 ∈ C := by
      rw [hC]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨z, by
          rw [hPtC]
          exact Finset.mem_filter.mpr ⟨hz, hne⟩, rfl⟩)))
    have h2 := hρlt _ hmem
    linarith
  -- Geometric consequences.
  have hdisj_ball : ∀ z ∈ S, z ≠ t₀ → ∀ w : ℂ, dist w z < ρ → dist w t₀ < δ → False := by
    intro z hz hne w hwz hwt
    have h1 : dist z t₀ ≤ dist z w + dist w t₀ := dist_triangle _ _ _
    have h2 : dist z w = dist w z := dist_comm _ _
    have h3 := hρfar z hz hne
    linarith
  have hdisj_pair : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → ∀ w : ℂ,
      dist w z < ρ → dist w z' < ρ → False := by
    intro z hz z' hz' hne w hwz hwz'
    have h1 : dist z z' ≤ dist z w + dist w z' := dist_triangle _ _ _
    have h2 := hρpair z hz z' hz' hne
    have h3 : dist z w = dist w z := dist_comm _ _
    linarith
  -- Nonvanishing of the two limit polynomials on the circles of radius `ρ`.
  have hnoF : ∀ z ∈ S, ∀ w : ℂ, dist w z = ρ → (F x₀).eval w ≠ 0 := by
    intro z hz w hw h0
    have hwS : w ∈ S :=
      Finset.mem_union_left _ ((hmF w).mpr (Polynomial.IsRoot.def.mpr h0))
    have hne : z ≠ w := by
      intro h
      rw [h] at hw
      rw [dist_self] at hw
      linarith
    have h2 := hρpair z hz w hwS hne
    rw [dist_comm] at h2
    linarith
  have hnoG : ∀ z ∈ S, ∀ w : ℂ, dist w z = ρ → (G x₀).eval w ≠ 0 := by
    intro z hz w hw h0
    have hwS : w ∈ S :=
      Finset.mem_union_right _ ((hmG w).mpr (Polynomial.IsRoot.def.mpr h0))
    have hne : z ≠ w := by
      intro h
      rw [h] at hw
      rw [dist_self] at hw
      linarith
    have h2 := hρpair z hz w hwS hne
    rw [dist_comm] at h2
    linarith
  -- Eventually the multiplicity of each fibre in each disk equals the multiplicity at `x₀`.
  have hdiskF : ∀ᶠ n in Filter.atTop, ∀ z ∈ S,
      ((F (x n)).roots.filter (fun w => dist w z < ρ)).card
        = ((F x₀).roots.filter (fun w => dist w z < ρ)).card := by
    rw [Filter.eventually_all_finset]
    intro z hz
    exact hx.eventually (disk_roots_card_eventually_const F d hcontF x₀
      (Filter.Eventually.of_forall hdegF) hρpos (hnoF z hz))
  have hdiskG : ∀ᶠ n in Filter.atTop, ∀ z ∈ S,
      ((G (x n)).roots.filter (fun w => dist w z < ρ)).card
        = ((G x₀).roots.filter (fun w => dist w z < ρ)).card := by
    rw [Filter.eventually_all_finset]
    intro z hz
    exact hx.eventually (disk_roots_card_eventually_const G d hcontG x₀
      (Filter.Eventually.of_forall hdegG) hρpos (hnoG z hz))
  filter_upwards [hdiskF, hdiskG] with n hdF hdG
  -- ## The fibre at `n`
  have hFnz : F (x n) ≠ 0 := by
    intro h0
    have h1 : (F (x n)).roots.toFinset.card = RF.card := hcardF n
    have h2 : (F (x n)).roots.toFinset.card = 0 := by rw [h0]; simp
    have h3 : 0 < RF.card := Finset.card_pos.mpr ⟨t₀, htF⟩
    omega
  have hGnz : G (x n) ≠ 0 := by
    intro h0
    have h1 : (G (x n)).roots.toFinset.card = RG.card := hcardG n
    have h2 : (G (x n)).roots.toFinset.card = 0 := by rw [h0]; simp
    have h3 : 0 < RG.card := Finset.card_pos.mpr ⟨t₀, htG⟩
    omega
  -- Multiplicities at `x₀` inside the disks are positive.
  have hcountF0 : ∀ z ∈ RF, 1 ≤ ((F x₀).roots.filter (fun w => dist w z < ρ)).card := by
    intro z hz
    have hzmem : z ∈ (F x₀).roots.filter (fun w => dist w z < ρ) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hF).mpr ((hmF z).mp hz),
        by rw [dist_self]; exact hρpos⟩
    have h : 0 < ((F x₀).roots.filter (fun w => dist w z < ρ)).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨z, hzmem⟩
    omega
  have hcountG0 : ∀ z ∈ RG, 1 ≤ ((G x₀).roots.filter (fun w => dist w z < ρ)).card := by
    intro z hz
    have hzmem : z ∈ (G x₀).roots.filter (fun w => dist w z < ρ) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hG).mpr ((hmG z).mp hz),
        by rw [dist_self]; exact hρpos⟩
    have h : 0 < ((G x₀).roots.filter (fun w => dist w z < ρ)).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨z, hzmem⟩
    omega
  have hcountFn : ∀ z ∈ RF, 1 ≤ ((F (x n)).roots.filter (fun w => dist w z < ρ)).card := by
    intro z hz
    have h1 := hdF z (Finset.mem_union_left _ hz)
    have h2 := hcountF0 z hz
    omega
  have hcountGn : ∀ z ∈ RG, 1 ≤ ((G (x n)).roots.filter (fun w => dist w z < ρ)).card := by
    intro z hz
    have h1 := hdG z (Finset.mem_union_right _ hz)
    have h2 := hcountG0 z hz
    omega
  -- Each disk of `RF` contains a root of `F (x n)`; choose one.
  have hrootF : ∀ z ∈ RF, ∃ w : ℂ, dist w z < ρ ∧ (F (x n)).IsRoot w := by
    intro z hz
    have hpos : 0 < ((F (x n)).roots.filter (fun w => dist w z < ρ)).card := by
      have := hcountFn z hz
      omega
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hwmem, hwd⟩ := Multiset.mem_filter.mp hw
    exact ⟨w, hwd, (Polynomial.mem_roots hFnz).mp hwmem⟩
  have hrootG : ∀ z ∈ RG, ∃ w : ℂ, dist w z < ρ ∧ (G (x n)).IsRoot w := by
    intro z hz
    have hpos : 0 < ((G (x n)).roots.filter (fun w => dist w z < ρ)).card := by
      have := hcountGn z hz
      omega
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hwmem, hwd⟩ := Multiset.mem_filter.mp hw
    exact ⟨w, hwd, (Polynomial.mem_roots hGnz).mp hwmem⟩
  have hchF : ∀ z : ℂ, ∃ w : ℂ, z ∈ RF → (dist w z < ρ ∧ (F (x n)).IsRoot w) := by
    intro z
    by_cases hz : z ∈ RF
    · obtain ⟨w, hw1, hw2⟩ := hrootF z hz
      exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  have hchG : ∀ z : ℂ, ∃ w : ℂ, z ∈ RG → (dist w z < ρ ∧ (G (x n)).IsRoot w) := by
    intro z
    by_cases hz : z ∈ RG
    · obtain ⟨w, hw1, hw2⟩ := hrootG z hz
      exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
    · exact ⟨0, fun hz' => absurd hz' hz⟩
  choose a ha using hchF
  choose b hb using hchG
  have ha' : ∀ z ∈ RF, dist (a z) z < ρ ∧ (F (x n)).IsRoot (a z) := fun z hz => ha z hz
  have hb' : ∀ z ∈ RG, dist (b z) z < ρ ∧ (G (x n)).IsRoot (b z) := fun z hz => hb z hz
  -- The chosen roots are distinct, and they exhaust the roots of the fibres.
  have hinjF : ∀ z ∈ RF, ∀ z' ∈ RF, a z = a z' → z = z' := by
    intro z hz z' hz' heq
    by_contra hne
    have h2 := hρpair z (Finset.mem_union_left _ hz) z' (Finset.mem_union_left _ hz') hne
    have h1 : dist z z' ≤ dist z (a z) + dist (a z) z' := dist_triangle _ _ _
    have h3 : dist z (a z) = dist (a z) z := dist_comm _ _
    have h4 : dist (a z) z' = dist (a z') z' := by rw [heq]
    have h5 := (ha' z hz).1
    have h6 := (ha' z' hz').1
    linarith
  have hinjG : ∀ z ∈ RG, ∀ z' ∈ RG, b z = b z' → z = z' := by
    intro z hz z' hz' heq
    by_contra hne
    have h2 := hρpair z (Finset.mem_union_right _ hz) z' (Finset.mem_union_right _ hz') hne
    have h1 : dist z z' ≤ dist z (b z) + dist (b z) z' := dist_triangle _ _ _
    have h3 : dist z (b z) = dist (b z) z := dist_comm _ _
    have h4 : dist (b z) z' = dist (b z') z' := by rw [heq]
    have h5 := (hb' z hz).1
    have h6 := (hb' z' hz').1
    linarith
  have hinjF' : Set.InjOn a (RF : Set ℂ) := fun z hz z' hz' heq => hinjF z hz z' hz' heq
  have hinjG' : Set.InjOn b (RG : Set ℂ) := fun z hz z' hz' heq => hinjG z hz z' hz' heq
  have hcardimgF : (RF.image a).card = RF.card := Finset.card_image_of_injOn hinjF'
  have hcardimgG : (RG.image b).card = RG.card := Finset.card_image_of_injOn hinjG'
  have hsubF : RF.image a ⊆ (F (x n)).roots.toFinset := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hFnz).mpr (ha' z hz).2)
  have hsubG : RG.image b ⊆ (G (x n)).roots.toFinset := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hGnz).mpr (hb' z hz).2)
  have hcardFn : (F (x n)).roots.toFinset.card = RF.card := hcardF n
  have hcardGn : (G (x n)).roots.toFinset.card = RG.card := hcardG n
  have himgF : RF.image a = (F (x n)).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsubF (by rw [hcardFn, hcardimgF])
  have himgG : RG.image b = (G (x n)).roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsubG (by rw [hcardGn, hcardimgG])
  have hrootInF : ∀ w : ℂ, (F (x n)).IsRoot w → w ∈ RF.image a := by
    intro w hw
    rw [himgF]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hFnz).mpr hw)
  have hrootInG : ∀ w : ℂ, (G (x n)).IsRoot w → w ∈ RG.image b := by
    intro w hw
    rw [himgG]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hGnz).mpr hw)
  -- The unique root of each fibre inside the `δ`-ball.
  have huniqF : ∀ w : ℂ, (F (x n)).IsRoot w → dist w t₀ < δ → w = a t₀ := by
    intro w hw hwd
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp (hrootInF w hw)
    have hzt : z = t₀ := by
      by_contra hne
      refine hdisj_ball z (Finset.mem_union_left _ hz) hne (a z) (ha' z hz).1 ?_
      rw [hzw]
      exact hwd
    rw [← hzw, hzt]
  have huniqG : ∀ w : ℂ, (G (x n)).IsRoot w → dist w t₀ < δ → w = b t₀ := by
    intro w hw hwd
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp (hrootInG w hw)
    have hzt : z = t₀ := by
      by_contra hne
      refine hdisj_ball z (Finset.mem_union_right _ hz) hne (b z) (hb' z hz).1 ?_
      rw [hzw]
      exact hwd
    rw [← hzw, hzt]
  -- ## The gcd argument
  let h : Polynomial ℂ := gcd (F (x n)) (G (x n))
  let h₀ : Polynomial ℂ := gcd (F x₀) (G x₀)
  have hhne : h ≠ 0 := gcd_ne_zero_of_left hFnz
  have hh0ne : h₀ ≠ 0 := gcd_ne_zero_of_left hF
  let R : Finset ℂ := RF ∩ RG
  have hdisjR : ∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → ∀ w : ℂ,
      dist w z < ρ → dist w z' < ρ → False := by
    intro z hz z' hz' hne w hw hw'
    exact hdisj_pair z (Finset.mem_union_left _ (Finset.mem_inter.mp hz).1)
      z' (Finset.mem_union_left _ (Finset.mem_inter.mp hz').1) hne w hw hw'
  -- Every root of the gcd is a common root of the two fibres, hence lies in one of the disks.
  have hcovh : ∀ w ∈ h.roots, ∃ z ∈ R, dist w z < ρ := by
    intro w hw
    have hwr : h.IsRoot w := (Polynomial.mem_roots hhne).mp hw
    have hwF : (F (x n)).IsRoot w := hwr.dvd (gcd_dvd_left _ _)
    have hwG : (G (x n)).IsRoot w := hwr.dvd (gcd_dvd_right _ _)
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp (hrootInF w hwF)
    obtain ⟨z', hz', hz'w⟩ := Finset.mem_image.mp (hrootInG w hwG)
    have hzeq : z = z' := by
      by_contra hne
      refine hdisj_pair z (Finset.mem_union_left _ hz) z' (Finset.mem_union_right _ hz') hne w ?_ ?_
      · rw [← hzw]
        exact (ha' z hz).1
      · rw [← hz'w]
        exact (hb' z' hz').1
    exact ⟨z, Finset.mem_inter.mpr ⟨hz, hzeq ▸ hz'⟩, by rw [← hzw]; exact (ha' z hz).1⟩
  have hcovh0 : ∀ w ∈ h₀.roots, ∃ z ∈ R, dist w z < ρ := by
    intro w hw
    have hwr : h₀.IsRoot w := (Polynomial.mem_roots hh0ne).mp hw
    have hwF : (F x₀).IsRoot w := hwr.dvd (gcd_dvd_left _ _)
    have hwG : (G x₀).IsRoot w := hwr.dvd (gcd_dvd_right _ _)
    exact ⟨w, Finset.mem_inter.mpr ⟨(hmF w).mpr hwF, (hmG w).mpr hwG⟩,
      by rw [dist_self]; exact hρpos⟩
  have hsumh : h.roots.card = ∑ z ∈ R, ((h.roots.filter (fun w => dist w z < ρ)).card) :=
    multiset_card_eq_sum_filter_of_disjoint h.roots R (fun z w => dist w z < ρ) hdisjR hcovh
  have hsumh0 : h₀.roots.card = ∑ z ∈ R, ((h₀.roots.filter (fun w => dist w z < ρ)).card) :=
    multiset_card_eq_sum_filter_of_disjoint h₀.roots R (fun z w => dist w z < ρ) hdisjR hcovh0
  have hcardh : h.roots.card = h.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcardh0 : h₀.roots.card = h₀.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hdegeq : h.natDegree = h₀.natDegree := hgcd n
  -- The disk count bounds each summand termwise ...
  have htermle : ∀ z ∈ R, ((h.roots.filter (fun w => dist w z < ρ)).card)
      ≤ min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
            (((G x₀).roots.filter (fun w => dist w z < ρ)).card) := by
    intro z hz
    obtain ⟨hzF, hzG⟩ := Finset.mem_inter.mp hz
    have hle1 : ((h.roots.filter (fun w => dist w z < ρ)).card)
        ≤ ((F (x n)).roots.filter (fun w => dist w z < ρ)).card :=
      Multiset.card_le_card (Multiset.filter_le_filter (fun w => dist w z < ρ)
        (Polynomial.roots.le_of_dvd hFnz (gcd_dvd_left _ _)))
    have hle2 : ((h.roots.filter (fun w => dist w z < ρ)).card)
        ≤ ((G (x n)).roots.filter (fun w => dist w z < ρ)).card :=
      Multiset.card_le_card (Multiset.filter_le_filter (fun w => dist w z < ρ)
        (Polynomial.roots.le_of_dvd hGnz (gcd_dvd_right _ _)))
    have hd1 := hdF z (Finset.mem_union_left _ hzF)
    have hd2 := hdG z (Finset.mem_union_right _ hzG)
    rw [hd1] at hle1
    rw [hd2] at hle2
    exact le_min hle1 hle2
  -- ... and the sum over all disks is exactly the degree of the gcd at `x₀`.
  have htermeq : ∀ z ∈ R, ((h₀.roots.filter (fun w => dist w z < ρ)).card)
      = min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
            (((G x₀).roots.filter (fun w => dist w z < ρ)).card) := by
    intro z hz
    obtain ⟨hzF, hzG⟩ := Finset.mem_inter.mp hz
    have hisoF : ∀ w : ℂ, (F x₀).IsRoot w → dist w z < ρ → w = z := by
      intro w hw hwd
      by_contra hne
      have h2 := hρpair z (Finset.mem_union_left _ hzF) w
        (Finset.mem_union_left _ ((hmF w).mpr hw)) (Ne.symm hne)
      rw [dist_comm] at h2
      linarith
    have hisoG : ∀ w : ℂ, (G x₀).IsRoot w → dist w z < ρ → w = z := by
      intro w hw hwd
      by_contra hne
      have h2 := hρpair z (Finset.mem_union_right _ hzG) w
        (Finset.mem_union_right _ ((hmG w).mpr hw)) (Ne.symm hne)
      rw [dist_comm] at h2
      linarith
    have hisoh0 : ∀ w : ℂ, h₀.IsRoot w → dist w z < ρ → w = z := by
      intro w hw hwd
      exact hisoF w (hw.dvd (gcd_dvd_left _ _)) hwd
    have e1 : (h₀.roots.filter (fun w => dist w z < ρ)).card = h₀.rootMultiplicity z :=
      roots_filter_card_eq_rootMultiplicity hh0ne hρpos hisoh0
    have e2 : ((F x₀).roots.filter (fun w => dist w z < ρ)).card = (F x₀).rootMultiplicity z :=
      roots_filter_card_eq_rootMultiplicity hF hρpos hisoF
    have e3 : ((G x₀).roots.filter (fun w => dist w z < ρ)).card = (G x₀).rootMultiplicity z :=
      roots_filter_card_eq_rootMultiplicity hG hρpos hisoG
    have e4 : h₀.rootMultiplicity z = min ((F x₀).rootMultiplicity z) ((G x₀).rootMultiplicity z) :=
      rootMultiplicity_gcd_complex (F x₀) (G x₀) hF hG z
    rw [e1, e2, e3, e4]
  have heq : (∑ z ∈ R, ((h.roots.filter (fun w => dist w z < ρ)).card))
      = ∑ z ∈ R, min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
          (((G x₀).roots.filter (fun w => dist w z < ρ)).card) := by
    have A : (∑ z ∈ R, ((h.roots.filter (fun w => dist w z < ρ)).card)) = h.roots.card :=
      hsumh.symm
    have B : h.roots.card = h₀.roots.card := by rw [hcardh, hcardh0, hdegeq]
    have Cc : h₀.roots.card = ∑ z ∈ R, ((h₀.roots.filter (fun w => dist w z < ρ)).card) := hsumh0
    have Dd : (∑ z ∈ R, ((h₀.roots.filter (fun w => dist w z < ρ)).card))
        = ∑ z ∈ R, min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
            (((G x₀).roots.filter (fun w => dist w z < ρ)).card) :=
      Finset.sum_congr rfl (fun z hz => htermeq z hz)
    rw [A, B, Cc, Dd]
  -- Equality of the sums forces equality of every summand.
  have htermeq' : ∀ z ∈ R, ((h.roots.filter (fun w => dist w z < ρ)).card)
      = min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
            (((G x₀).roots.filter (fun w => dist w z < ρ)).card) := by
    intro z hz
    by_contra hne
    have hlt : ((h.roots.filter (fun w => dist w z < ρ)).card)
        < min (((F x₀).roots.filter (fun w => dist w z < ρ)).card)
              (((G x₀).roots.filter (fun w => dist w z < ρ)).card) :=
      lt_of_le_of_ne (htermle z hz) hne
    have hsumlt := Finset.sum_lt_sum htermle ⟨z, hz, hlt⟩
    rw [heq] at hsumlt
    exact absurd hsumlt (lt_irrefl _)
  -- In particular the gcd has a root in the disk around `t₀`.
  have ht₀R : t₀ ∈ R := Finset.mem_inter.mpr ⟨htF, htG⟩
  have hpos : 0 < ((h.roots.filter (fun w => dist w t₀ < ρ)).card) := by
    rw [htermeq' t₀ ht₀R]
    exact lt_of_lt_of_le Nat.zero_lt_one (le_min (hcountF0 t₀ htF) (hcountG0 t₀ htG))
  obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨hwr, hwd⟩ := Multiset.mem_filter.mp hw
  have hwF : (F (x n)).IsRoot w := ((Polynomial.mem_roots hhne).mp hwr).dvd (gcd_dvd_left _ _)
  have hwG : (G (x n)).IsRoot w := ((Polynomial.mem_roots hhne).mp hwr).dvd (gcd_dvd_right _ _)
  have hwδ : dist w t₀ < δ := by linarith [hwd, hρδ]
  have hwa : w = a t₀ := huniqF w hwF hwδ
  have hwb : w = b t₀ := huniqG w hwG hwδ
  refine ⟨a t₀, ?_, (ha' t₀ htF).2, ?_, huniqF, ?_⟩
  · have h := (ha' t₀ htF).1
    linarith
  · rw [← hwa]
    exact hwG
  · intro w' hw' hw'δ
    have h1 : w' = b t₀ := huniqG w' hw' hw'δ
    rw [h1]
    exact hwb.symm.trans hwa

end Work.WilE4.CAD
