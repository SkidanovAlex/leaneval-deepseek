import Mathlib
import Submission.Work.BW.aligned_defs
import Submission.Work.BW.es2.waldschmidt_relation_bound
import Submission.Work.BW.circuit_hmin_subfamily
import Submission.Work.BW.F_bound_of_waldschmidt_sub_fixed
import Submission.Work.BW.relation_lattice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `exists_short_second_element_fixed` (Baker--Wüstholz, second short element)

Given a minimal ℚ-dependence `ℓ : Fin m → ℂ` of the logarithms of the `α i` (`hdep`, `hmin`),
a generator `r` of the kernel of `θ` on the relation lattice `Γ = GammaSub α hα` (`hr`), a
Waldschmidt-size bound on `r` (`hrb`), and the existence of some `y ∈ Γ` with `θ y ≠ 0`
(`hrank2`, so `Γ / ℤr` is nontrivial), the theorem produces a *second* element `u ∈ Γ`,
`θ u ≠ 0`, whose weighted norm together with that of `r` is below the full Waldschmidt bound
`(9 m d³)^m ∏ᵢ hmod (α i) (ℓ i) / 2`.

Proof architecture (see the body for details):

* `hrank2` gives `y₀` with `θ y₀ ≠ 0`, hence `2πi ∈ span_ℚ (range ℓ)` after dividing by the
  rational coordinate `q₀` of `y₀` (`muRelC_iff_exists_rat`).
* Take a `card`-minimal `κ ⊆ Fin m` with `2πi ∈ span_ℚ (ℓ '' κ)`.  Minimality gives that
  `(ℓ i)_{i ∈ κ}` is ℚ-linearly independent and that `2πi` is not in the span of the
  `ℓ i`, `i ∈ κ \ {j}`; `κ ≠ univ` gives `κ.card ≤ m - 1`.
* Apply Waldschmidt's relation bound to the family `(1, α i)_{i ∈ κ}` with logarithms
  `(2πi, ℓ i)`: `hdepf` (the `2πi` is dependent) and `hminf`
  (`circuit_hmin_subfamily`) are exactly its hypotheses.
* The resulting integer relation `t'` has `t' 0 ≠ 0` (`ht'0`), and after transporting it to
  `Fin m` (supported on `κ`) it becomes `u ∈ Γ` with `θ u = -(t' 0) · 2πi ≠ 0`; the
  coordinate bound of Waldschmidt gives the weighted-norm bound, and
  `F_bound_of_waldschmidt_sub_fixed` turns it into the pair bound, using the given bound on
  `r` (`hrb`) and `hker`/`hr` only through the final `linarith`.

The Kronecker/Waldschmidt input is taken from the self-contained copies in namespace
`Work.BW.es2` (modules `Submission/Work/BW/es2/*`).  These are frozen, verbatim copies of the
corresponding results in `Submission/Work/BW/` with identical statements, kept under the
`Work.BW.es2` namespace so that this file does not depend on the concurrently edited originals
(the axioms used are unchanged: `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Work.BW

open Complex

private lemma twoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero

private lemma hmod_nonneg_aux {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) :
    0 ≤ hmod β ℓ := by
  have hd : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by positivity
  rw [hmod]
  exact le_trans hd (le_trans (le_max_right _ _) (le_max_right _ _))

private lemma hmod_one_twoPiI {K : Type*} [Field K] [NumberField K] :
    hmod (1 : K) (2 * (Real.pi : ℂ) * Complex.I) ≤ 2 * Real.pi / (Module.finrank ℚ K : ℝ) := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  rw [hmod, Height.logHeight₁_one, zero_div, hnorm]
  refine max_le (by positivity) (max_le le_rfl ?_)
  rw [div_le_div_iff_of_pos_right hd]
  linarith [Real.pi_gt_three]

private lemma cons_not_linearIndependent {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : V) (g : Fin n → V) (hx : x ∈ Submodule.span ℚ (Set.range g)) (hx0 : x ≠ 0) :
    ¬ LinearIndependent ℚ (@Fin.cons n (fun _ => V) x g) := by
  intro h
  exact (linearIndependent_finCons.mp h).2 hx

theorem exists_short_second_element_fixed {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (φ : K →+* ℂ) (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j))
    (r : Fin m → ℤ) (hker : r ∈ GammaSub α hα)
    (hr : ∀ y : Fin m → ℤ, y ∈ GammaSub α hα → thetaC ℓ y = 0 → ∃ a : ℤ, y = a • r)
    (hrb : wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m *
        (∏ i, hmod (α i) (ℓ i)) / (9 * (Module.finrank ℚ K : ℝ) ^ 2))
    (hrank2 : ∃ y : Fin m → ℤ, y ∈ GammaSub α hα ∧ thetaC ℓ y ≠ 0) :
    ∃ u : Fin m → ℤ, u ∈ GammaSub α hα ∧ thetaC ℓ u ≠ 0 ∧
      wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) u +
      wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
        (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m *
          (∏ i, hmod (α i) (ℓ i)) / 2 := by
  classical
  set twoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I with htwoPiI
  have h2ne : twoPiI ≠ 0 := by rw [htwoPiI]; exact twoPiI_ne_zero
  have hexp2 : Complex.exp twoPiI = 1 := by rw [htwoPiI]; exact Complex.exp_two_pi_mul_I
  by_cases hm : 2 ≤ m
  · obtain ⟨y₀, hy₀Γ, hy₀θ⟩ := hrank2
    obtain ⟨q₀, hq₀⟩ := (muRelC_iff_exists_rat φ α ℓ hℓ y₀).mp hy₀Γ
    have hq₀ne : q₀ ≠ 0 := by
      rintro rfl
      simp only [Rat.cast_zero, zero_mul] at hq₀
      exact hy₀θ hq₀
    have hq₀C : (q₀ : ℂ) ≠ 0 := by exact_mod_cast hq₀ne
    have hspan2 : twoPiI ∈ Submodule.span ℚ (Set.range ℓ) := by
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => (y₀ i : ℚ) / q₀, ?_⟩
      have hsum : ∑ i, ((y₀ i : ℚ) / q₀) • ℓ i
          = ((q₀ : ℂ))⁻¹ * ∑ i, (y₀ i : ℂ) * ℓ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def]
        change (((y₀ i : ℚ) / q₀ : ℚ) : ℂ) * ℓ i = (q₀ : ℂ)⁻¹ * ((y₀ i : ℂ) * ℓ i)
        rw [Rat.cast_div, Rat.cast_intCast]
        ring
      rw [hsum, ← thetaC, hq₀]
      rw [htwoPiI]
      field_simp
    set S : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powerset.filter
      (fun s => twoPiI ∈ Submodule.span ℚ (ℓ '' (↑s : Set (Fin m)))) with hS
    have hSne : S.Nonempty := by
      refine ⟨Finset.univ, ?_⟩
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.Subset.refl _, ?_⟩
      rw [show (ℓ '' (↑(Finset.univ : Finset (Fin m)) : Set (Fin m))) = Set.range ℓ from by
        ext x; simp]
      exact hspan2
    obtain ⟨κ, hκS, hκmin⟩ := Finset.exists_min_image S Finset.card hSne
    rw [hS, Finset.mem_filter, Finset.mem_powerset] at hκS
    obtain ⟨hκsub, hκspan⟩ := hκS
    have hκne : κ.Nonempty := by
      rcases Finset.eq_empty_or_nonempty κ with h | h
      · exfalso
        rw [h] at hκspan
        have hz : twoPiI = 0 := by simpa using hκspan
        exact h2ne hz
      · exact h
    have hκLI : LinearIndependent ℚ (fun i : {i // i ∈ κ} => ℓ i) := by
      rw [linearIndependent_iff']
      intro s g hg i₀ hi₀
      by_contra hne
      have hslack : ℓ (i₀ : Fin m) ∈
          Submodule.span ℚ (ℓ '' (↑(κ.erase (i₀ : Fin m)) : Set (Fin m))) := by
        have hsp : g i₀ • ℓ (i₀ : Fin m) = -∑ i ∈ s.erase i₀, g i • ℓ (i : Fin m) := by
          have h1 := Finset.sum_erase_add s (fun i => g i • ℓ ((i : {i // i ∈ κ}) : Fin m)) hi₀
          rw [hg] at h1
          exact eq_neg_of_add_eq_zero_right h1
        have hmem : g i₀ • ℓ (i₀ : Fin m) ∈
            Submodule.span ℚ (ℓ '' (↑(κ.erase (i₀ : Fin m)) : Set (Fin m))) := by
          rw [hsp]
          refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
          have hne' : (i : Fin m) ≠ (i₀ : Fin m) :=
            fun hc => (Finset.mem_erase.mp hi).1 (Subtype.ext hc)
          exact Submodule.subset_span ⟨(i : Fin m), Finset.mem_erase.mpr ⟨hne', i.property⟩, rfl⟩
        have h2 := Submodule.smul_mem _ ((g i₀)⁻¹) hmem
        rwa [inv_smul_smul₀ hne (ℓ (i₀ : Fin m))] at h2
      have hle : Submodule.span ℚ (ℓ '' (↑κ : Set (Fin m)))
          ≤ Submodule.span ℚ (ℓ '' (↑(κ.erase (i₀ : Fin m)) : Set (Fin m))) := by
        rw [Submodule.span_le]
        rintro y ⟨i, hi, rfl⟩
        by_cases h : i = (i₀ : Fin m)
        · subst h; exact hslack
        · exact Submodule.subset_span ⟨i, Finset.mem_erase.mpr ⟨h, hi⟩, rfl⟩
      have h2span := hle hκspan
      have hmem : κ.erase (i₀ : Fin m) ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.subset_univ _, h2span⟩
      have hlt := hκmin (κ.erase (i₀ : Fin m)) hmem
      rw [Finset.card_erase_of_mem i₀.property] at hlt
      have hpos : 0 < κ.card := Finset.card_pos.mpr ⟨i₀, i₀.property⟩
      omega
    have hκne_univ : κ ≠ Finset.univ := by
      intro h
      apply hdep
      rw [h] at hκLI
      rw [Fintype.linearIndependent_iff] at hκLI ⊢
      intro g hg i
      have h1 := hκLI (fun j : {j : Fin m // (j : Fin m) ∈ Finset.univ} => g (j : Fin m))
      have hsum : ∑ j : {j : Fin m // (j : Fin m) ∈ Finset.univ},
            g (j : Fin m) • ℓ (j : Fin m) = ∑ j, g j • ℓ j :=
        (Finset.sum_subtype (Finset.univ) (fun x => Iff.rfl) (fun j => g j • ℓ j)).symm
      have hz : ∑ j : {j : Fin m // (j : Fin m) ∈ Finset.univ},
            g (j : Fin m) • ℓ (j : Fin m) = 0 := by rw [hsum]; exact hg
      exact h1 hz ⟨i, Finset.mem_univ i⟩
    have hκcard : κ.card ≤ m - 1 := by
      have hlt : κ.card < (Finset.univ : Finset (Fin m)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hκsub, hκne_univ⟩)
      rw [Finset.card_univ, Fintype.card_fin] at hlt
      omega
    set n : ℕ := κ.card with hn
    let e : Fin n ≃ {i // i ∈ κ} := (Finset.equivFin κ).symm
    let gg : Fin n → ℂ := fun b => ℓ ((e b : {i // i ∈ κ}) : Fin m)
    have hLI_g : LinearIndependent ℚ gg := (linearIndependent_equiv e).mpr hκLI
    have hx_min : ∀ b : Fin n, twoPiI ∉ Submodule.span ℚ
        (Set.range (fun b' : {b' : Fin n // (b' : Fin n) ≠ b} => gg b')) := by
      intro b hmem
      have hrange : Set.range (fun b' : {b' : Fin n // (b' : Fin n) ≠ b} => gg b')
          = ℓ '' (↑(κ.erase ((e b).val)) : Set (Fin m)) := by
        ext x
        constructor
        · rintro ⟨b', rfl⟩
          refine ⟨(e b').val, Finset.mem_erase.mpr ⟨?_, (e b').property⟩, rfl⟩
          intro hc
          exact b'.property (e.injective (Subtype.ext hc))
        · rintro ⟨i, hi, rfl⟩
          obtain ⟨hij, hiκ⟩ := Finset.mem_erase.mp hi
          refine ⟨⟨e.symm ⟨i, hiκ⟩, ?_⟩, ?_⟩
          · intro hc
            refine hij ?_
            have h1 : e (e.symm ⟨i, hiκ⟩) = e b := by rw [hc]
            rw [Equiv.apply_symm_apply] at h1
            exact congrArg Subtype.val h1
          · show gg (e.symm ⟨i, hiκ⟩) = ℓ i
            dsimp only [gg]
            rw [Equiv.apply_symm_apply e ⟨i, hiκ⟩]
      rw [hrange] at hmem
      have hmemS : κ.erase ((e b).val) ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.subset_univ _, hmem⟩
      have hlt := hκmin (κ.erase ((e b).val)) hmemS
      rw [Finset.card_erase_of_mem (e b).property] at hlt
      have hpos : 0 < κ.card := Finset.card_pos.mpr ⟨(e b).val, (e b).property⟩
      omega
    let ℓf : Fin (n + 1) → ℂ := @Fin.cons n (fun _ => ℂ) twoPiI gg
    let αf : Fin (n + 1) → K := @Fin.cons n (fun _ => K) (1 : K)
      (fun b => α ((e b : {i // i ∈ κ}) : Fin m))
    have hαf0 : αf 0 = 1 := by
      rw [show αf = (@Fin.cons n (fun _ => K) (1 : K)
        (fun b => α ((e b : {i // i ∈ κ}) : Fin m))) from rfl]
      exact Fin.cons_zero _ _
    have hαfs : ∀ b, αf b.succ = α ((e b : {i // i ∈ κ}) : Fin m) := by
      intro b
      rw [show αf = (@Fin.cons n (fun _ => K) (1 : K)
        (fun b => α ((e b : {i // i ∈ κ}) : Fin m))) from rfl]
      exact Fin.cons_succ _ _ _
    have hαf : ∀ a, αf a ≠ 0 := by
      intro a
      refine Fin.cases ?_ (fun b => ?_) a
      · rw [hαf0]; exact one_ne_zero
      · rw [hαfs b]; exact hα _
    have hℓf0 : ℓf 0 = twoPiI := by
      rw [show ℓf = (@Fin.cons n (fun _ => ℂ) twoPiI gg) from rfl]
      exact Fin.cons_zero _ _
    have hℓfs : ∀ b, ℓf b.succ = gg b := by
      intro b
      rw [show ℓf = (@Fin.cons n (fun _ => ℂ) twoPiI gg) from rfl]
      exact Fin.cons_succ _ _ _
    have hℓf : ∀ a, Complex.exp (ℓf a) = φ (αf a) := by
      intro a
      refine Fin.cases ?_ (fun b => ?_) a
      · rw [hℓf0, hexp2, hαf0, map_one]
      · rw [hℓfs b, hαfs b]
        exact hℓ _
    have hdepf : ¬ LinearIndependent ℚ ℓf := by
      have hx : twoPiI ∈ Submodule.span ℚ (Set.range gg) := by
        have hr : Set.range gg = ℓ '' (↑κ : Set (Fin m)) := by
          ext x
          constructor
          · rintro ⟨b, rfl⟩
            exact ⟨(e b).val, (e b).property, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            refine ⟨e.symm ⟨i, hi⟩, ?_⟩
            show gg (e.symm ⟨i, hi⟩) = ℓ i
            dsimp only [gg]
            rw [Equiv.apply_symm_apply]
        rw [hr]; exact hκspan
      exact cons_not_linearIndependent twoPiI gg hx h2ne
    have hminf : ∀ a : Fin (n + 1),
        LinearIndependent ℚ (fun j : {j : Fin (n + 1) // j ≠ a} => ℓf j) :=
      circuit_hmin_subfamily twoPiI gg hLI_g hx_min
    obtain ⟨t', ht'ne, ht'rel, ht'bnd⟩ :=
      es2.waldschmidt_relation_bound φ αf hαf ℓf hℓf hdepf hminf
    have ht'0 : t' 0 ≠ 0 := by
      intro h0
      apply ht'ne
      funext a
      have hzero : ∑ b : Fin n, (t' b.succ : ℂ) * gg b = 0 := by
        have hsplit := Fin.sum_univ_succ (fun a => (t' a : ℂ) * ℓf a)
        rw [ht'rel] at hsplit
        rw [hℓf0] at hsplit
        rw [h0] at hsplit
        simp only [Int.cast_zero, zero_mul, zero_add] at hsplit
        rw [show (∑ b : Fin n, (t' b.succ : ℂ) * ℓf b.succ)
              = ∑ b : Fin n, (t' b.succ : ℂ) * gg b from
            Finset.sum_congr rfl fun b _ => by
              rw [hℓfs b]] at hsplit
        exact hsplit.symm
      have hz : ∑ b : Fin n, (t' b.succ : ℚ) • gg b = 0 := by
        rw [← hzero]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Algebra.smul_def]
        change (((t' b.succ : ℤ) : ℚ) : ℂ) * gg b = ((t' b.succ : ℤ) : ℂ) * gg b
        rw [Rat.cast_intCast]
      refine Fin.cases h0 (fun b => ?_) a
      exact_mod_cast (Fintype.linearIndependent_iff.mp hLI_g) (fun b => (t' b.succ : ℚ)) hz b
    let u : Fin m → ℤ := fun i => if h : i ∈ κ then t' (Fin.succ (e.symm ⟨i, h⟩)) else 0
    have hsupp : ∀ i, i ∉ κ → u i = 0 := by
      intro i hi; simp only [u, dif_neg hi]
    have hu_eq : ∀ b : Fin n, u ((e b).val) = t' b.succ := by
      intro b
      simp only [u, dif_pos (e b).property]
      rw [show (⟨(e b).val, (e b).property⟩ : {i // i ∈ κ}) = e b from rfl,
        Equiv.symm_apply_apply]
    have htheta_u : thetaC ℓ u = -((t' 0 : ℤ) : ℂ) * twoPiI := by
      have h1 : thetaC ℓ u = ∑ b : Fin n, (t' b.succ : ℂ) * gg b := by
        rw [thetaC]
        rw [show (∑ i, (u i : ℂ) * ℓ i) = ∑ i ∈ κ, (u i : ℂ) * ℓ i from
          (Finset.sum_subset (Finset.subset_univ κ) (fun i _ hi => by simp [u, hi])).symm]
        rw [← Finset.sum_coe_sort]
        exact (Fintype.sum_equiv e (fun b : Fin n => (t' b.succ : ℂ) * gg b)
          (fun i : {i // i ∈ κ} => (u (i : Fin m) : ℂ) * ℓ (i : Fin m))
          (fun b => by rw [hu_eq b])).symm
      rw [h1]
      have h2 := Fin.sum_univ_succ (fun a : Fin (n + 1) => (t' a : ℂ) * ℓf a)
      rw [ht'rel] at h2
      rw [hℓf0, show (∑ b : Fin n, (t' b.succ : ℂ) * ℓf b.succ)
            = ∑ b : Fin n, (t' b.succ : ℂ) * gg b from
          Finset.sum_congr rfl fun b _ => by rw [hℓfs b]] at h2
      have h3 := eq_neg_of_add_eq_zero_right (h2.symm)
      rw [h3]
      ring
    have huΓ : u ∈ GammaSub α hα := by
      rw [mem_GammaSub, muRelC_iff_exists_rat φ α ℓ hℓ]
      refine ⟨-((t' 0 : ℤ) : ℚ), ?_⟩
      rw [htheta_u]; push_cast; ring
    have huθ : thetaC ℓ u ≠ 0 := by
      rw [htheta_u]
      exact mul_ne_zero (neg_ne_zero.mpr (Int.cast_ne_zero.mpr ht'0)) h2ne
    have ht : ∀ j ∈ κ, |((u j : ℤ) : ℝ)| ≤
        (9 * ((κ.card : ℝ)) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (κ.card) *
          (2 * Real.pi / (Module.finrank ℚ K : ℝ)) *
            ∏ i ∈ κ.erase j, hmod (α i) (ℓ i) := by
      intro j hj
      have huj : u j = t' (Fin.succ (e.symm ⟨j, hj⟩)) := by simp only [u, dif_pos hj]
      have hk0 : Fin.succ (e.symm ⟨j, hj⟩) ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
      have hb : |((t' (Fin.succ (e.symm ⟨j, hj⟩)) : ℤ) : ℝ)| ≤
          (9 * (↑(n + 1) - 1) * ↑(Module.finrank ℚ K) ^ 3) ^ (n + 1 - 1) *
            ∏ a ∈ Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩)), hmod (αf a) (ℓf a) :=
        ht'bnd _
      rw [show n + 1 - 1 = n from by omega] at hb
      have h0 : hmod (αf 0) (ℓf 0) ≤ 2 * Real.pi / (Module.finrank ℚ K : ℝ) := by
        rw [hαf0, hℓf0]; exact hmod_one_twoPiI
      have hXnn : 0 ≤ ∏ i ∈ κ.erase j, hmod (α i) (ℓ i) :=
        Finset.prod_nonneg fun i _ => hmod_nonneg_aux _ _
      have hsplit : ∏ a ∈ Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩)),
            hmod (αf a) (ℓf a)
          = hmod (αf 0) (ℓf 0) *
            ∏ a ∈ (Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩))).erase 0,
              hmod (αf a) (ℓf a) := by
        rw [mul_comm]
        exact (Finset.prod_erase_mul (Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩)))
          (fun a => hmod (αf a) (ℓf a))
          (Finset.mem_erase.mpr ⟨hk0.symm, Finset.mem_univ _⟩)).symm
      have key : ∏ i ∈ κ.erase j, hmod (α i) (ℓ i)
          = ∏ a ∈ (Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩))).erase 0,
              hmod (αf a) (ℓf a) := by
        refine Finset.prod_bij (fun (i : Fin m) (hi : i ∈ κ.erase j) =>
          Fin.succ (e.symm ⟨i, (Finset.mem_erase.mp hi).2⟩)) ?_ ?_ ?_ ?_
        · intro i hi
          obtain ⟨hij, hiκ⟩ := Finset.mem_erase.mp hi
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨Fin.succ_ne_zero _, fun hc =>
            hij (Subtype.ext_iff.mp (e.symm.injective (Fin.succ_injective n hc)))⟩
        · intro i₁ hi₁ i₂ hi₂ heq
          exact Subtype.ext_iff.mp (e.symm.injective (Fin.succ_injective n heq))
        · intro b hb
          obtain ⟨hb0, hbk⟩ := Finset.mem_erase.mp hb
          obtain ⟨hbk', -⟩ := Finset.mem_erase.mp hbk
          obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb0
          have hb' : b' ≠ e.symm ⟨j, hj⟩ := fun hc => hbk' (by rw [hc])
          refine ⟨(e b').val, Finset.mem_erase.mpr ⟨?_, (e b').property⟩, ?_⟩
          · intro hc
            have h2 : e b' = (⟨j, hj⟩ : {i // i ∈ κ}) := Subtype.ext hc
            exact hb' (by rw [← h2, Equiv.symm_apply_apply])
          · show Fin.succ (e.symm ⟨(e b').val, (e b').property⟩) = Fin.succ b'
            rw [show (⟨(e b').val, (e b').property⟩ : {i // i ∈ κ}) = e b' from rfl,
              Equiv.symm_apply_apply]
        · intro i hi
          obtain ⟨hij, hiκ⟩ := Finset.mem_erase.mp hi
          rw [hαfs, hℓfs]
          dsimp only [gg]
          rw [Equiv.apply_symm_apply e ⟨i, hiκ⟩]
      have hbase : (9 : ℝ) * (↑(n + 1) - 1) * ↑(Module.finrank ℚ K) ^ 3
          = 9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3 := by rw [hn]; push_cast; ring
      have hpow : (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ n
          = (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) := by rw [hn]
      have hAnn : 0 ≤ (9 * (κ.card : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (κ.card) := by
        positivity
      calc |((u j : ℤ) : ℝ)|
          = |((t' (Fin.succ (e.symm ⟨j, hj⟩)) : ℤ) : ℝ)| := by rw [huj]
        _ ≤ (9 * (↑(n + 1) - 1) * ↑(Module.finrank ℚ K) ^ 3) ^ n *
              ∏ a ∈ Finset.univ.erase (Fin.succ (e.symm ⟨j, hj⟩)), hmod (αf a) (ℓf a) := hb
        _ = (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) *
              (hmod (αf 0) (ℓf 0) * ∏ i ∈ κ.erase j, hmod (α i) (ℓ i)) := by
              rw [hbase, hpow, hsplit, key.symm]
        _ ≤ (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) *
              (2 * Real.pi / ↑(Module.finrank ℚ K)) *
                ∏ i ∈ κ.erase j, hmod (α i) (ℓ i) := by
              have hstep := mul_le_mul_of_nonneg_right h0 hXnn
              have h2 := mul_le_mul_of_nonneg_left hstep hAnn
              calc (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) *
                      (hmod (αf 0) (ℓf 0) * ∏ i ∈ κ.erase j, hmod (α i) (ℓ i))
                  ≤ (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) *
                      ((2 * Real.pi / ↑(Module.finrank ℚ K)) *
                        ∏ i ∈ κ.erase j, hmod (α i) (ℓ i)) := h2
                _ = (9 * (κ.card : ℝ) * ↑(Module.finrank ℚ K) ^ 3) ^ (κ.card) *
                      (2 * Real.pi / ↑(Module.finrank ℚ K)) *
                        ∏ i ∈ κ.erase j, hmod (α i) (ℓ i) := by ring

    have hFB := F_bound_of_waldschmidt_sub_fixed α ℓ κ hκne hκcard u hsupp ht r hrb
    refine ⟨u, huΓ, huθ, ?_⟩
    have hhalf := hFB
    linarith [hhalf]
  · push_neg at hm
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · exact absurd (Fintype.linearIndependent_iff.mpr (fun g _ i => i.elim0)) hdep
    · have hℓ0 : ℓ 0 = 0 := by
        rw [Fintype.linearIndependent_iff] at hdep
        push_neg at hdep
        obtain ⟨g, hg, i, hgi⟩ := hdep
        have hg0 : g 0 ≠ 0 := by rwa [Subsingleton.elim i 0] at hgi
        have h1 : g 0 • ℓ 0 = 0 := by simpa using hg
        rcases smul_eq_zero.mp h1 with h | h
        · exact absurd h hg0
        · exact h
      exfalso
      obtain ⟨y₀, _, hy₀θ⟩ := hrank2
      apply hy₀θ
      rw [thetaC]
      simp [hℓ0]

end Work.BW
