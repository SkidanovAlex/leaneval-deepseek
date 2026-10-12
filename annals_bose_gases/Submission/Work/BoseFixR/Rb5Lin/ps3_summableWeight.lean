import Mathlib.Algebra.Module.ZLattice.Summable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.ps3_summableWeight`

Summability of the lattice weight `m ↦ (1 + ‖m‖)⁻⁴` over `ℤ³` (viewed as `Fin 3 → ℤ`
with the sup norm on `Fin 3 → ℝ`), which is the decay input for the Poisson-summation /
lattice-sum manipulations of the `ps3` family.

The proof embeds `ℤ³` into `ℝ³ = Fin 3 → ℝ` as the `ℤ`-span `L3` of the standard basis
(so that the ambient norm is *literally* the sup norm of the coordinates) and applies the
Mathlib lattice-summability theorem `ZLattice.summable_norm_pow_inv` with rank `3 < 4`.
The translation between the subtype `L3` and the coordinate picture `Fin 3 → ℤ` is by
`Summable.comp_injective`, and the single point `m = 0` is absorbed by an explicit delta
mass.
-/

open Module

noncomputable section

namespace Work.BoseFixR.Rb5Lin

/-- `ℤ³ ⊆ ℝ³` as the `ℤ`-span of the standard basis; the ambient norm is the sup norm. -/
private abbrev L3 : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

/-- The lattice `ℤ³` has `ℤ`-rank `3 < 4`. -/
private lemma finrank_L3 : Module.finrank ℤ L3 < 4 := by
  have hrank : Module.finrank ℤ L3 = Module.finrank ℝ (Fin 3 → ℝ) := ZLattice.rank ℝ L3
  rw [hrank, Module.finrank_fintype_fun_eq_card]
  norm_num

/-- `∑_{z ∈ ℤ³} ‖z‖⁻⁴ < ∞` (`ZLattice.summable_norm_pow_inv`, rank `3 < 4`). -/
private lemma summable_norm_inv_pow : Summable (fun z : L3 => ‖z‖⁻¹ ^ 4) :=
  ZLattice.summable_norm_pow_inv L3 4 finrank_L3

/-- The lattice point `n : Fin 3 → ℤ` as an element of the ambient space `ℝ³`. -/
private def toE (n : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (n i : ℝ)

private lemma mem_toE (n : Fin 3 → ℤ) : toE n ∈ L3 := by
  rw [Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin 3)) (toE n)]
  intro i
  exact ⟨n i, by rw [Pi.basisFun_repr]; rfl⟩

/-- The lattice point `n : Fin 3 → ℤ` viewed as an element of the lattice `L3`. -/
private def emb (n : Fin 3 → ℤ) : L3 := ⟨toE n, mem_toE n⟩

private lemma emb_injective : Function.Injective emb := by
  intro a b h
  funext i
  have hc := congrArg (fun z : L3 => (z : Fin 3 → ℝ) i) h
  simp only [emb, toE, Submodule.coe_mk] at hc
  exact_mod_cast hc

/-- The lattice series, re-indexed by the coordinate picture `Fin 3 → ℤ`. -/
private lemma summable_emb : Summable (fun n : Fin 3 → ℤ => ‖emb n‖⁻¹ ^ 4) := by
  have h0 := summable_norm_inv_pow.comp_injective (i := emb) emb_injective
  simpa [Function.comp_def] using h0

/-- A non-zero integral vector has sup norm at least `1`. -/
private lemma norm_sup_pos {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    (1 : ℝ) ≤ ‖fun i : Fin 3 => (n i : ℝ)‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
  have h2 : (1 : ℝ) ≤ ‖(fun j : Fin 3 => (n j : ℝ)) i‖ := by
    rw [show (fun j : Fin 3 => (n j : ℝ)) i = (n i : ℝ) from rfl, Real.norm_eq_abs]
    exact_mod_cast (Int.one_le_abs hi)
  exact le_trans h2 (norm_le_pi_norm (fun j : Fin 3 => (n j : ℝ)) i)

/-- For `x ≥ 1` the weight `(1 + x)⁻⁴` is dominated by `x⁻⁴`. -/
private lemma inv_one_add_pow_le (x : ℝ) (hx : 1 ≤ x) : ((1 + x) ^ 4)⁻¹ ≤ x⁻¹ ^ 4 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : x ^ 4 ≤ (1 + x) ^ 4 := pow_le_pow_left₀ (le_of_lt hx0) (by linarith) 4
  calc ((1 + x) ^ 4)⁻¹ ≤ (x ^ 4)⁻¹ :=
        (inv_le_inv₀ (a := (1 + x) ^ 4) (b := x ^ 4) (by positivity) (by positivity)).mpr hpow
    _ = x⁻¹ ^ 4 := (inv_pow x 4).symm

/-- The pointwise domination of the weight by the lattice series plus the mass at `0`. -/
private lemma weight_le (n : Fin 3 → ℤ) :
    ((1 + ‖fun i : Fin 3 => (n i : ℝ)‖) ^ 4)⁻¹
      ≤ ‖emb n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0) := by
  by_cases hn : n = 0
  · subst hn
    simp [emb]
  · have hc1 : (1 : ℝ) ≤ ‖fun i : Fin 3 => (n i : ℝ)‖ := norm_sup_pos hn
    have h := inv_one_add_pow_le ‖fun i : Fin 3 => (n i : ℝ)‖ hc1
    calc ((1 + ‖fun i : Fin 3 => (n i : ℝ)‖) ^ 4)⁻¹
        ≤ ‖fun i : Fin 3 => (n i : ℝ)‖⁻¹ ^ 4 := h
      _ = ‖emb n‖⁻¹ ^ 4 := by rw [show ‖emb n‖ = ‖fun i : Fin 3 => (n i : ℝ)‖ from rfl]
      _ ≤ ‖emb n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0) := le_add_of_nonneg_right (by positivity)

theorem ps3_summableWeight :
    Summable (fun m : Fin 3 → ℤ => ((1 + ‖fun i : Fin 3 => (m i : ℝ)‖) ^ 4)⁻¹) := by
  have hdelta : Summable (fun n : Fin 3 → ℤ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (b := (0 : Fin 3 → ℤ)) (a := (1 : ℝ))).summable
  have hmaj : Summable (fun n : Fin 3 → ℤ =>
      ‖emb n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0)) := summable_emb.add hdelta
  refine Summable.of_nonneg_of_le
    (f := fun n : Fin 3 → ℤ => ‖emb n‖⁻¹ ^ 4 + (if n = 0 then (1 : ℝ) else 0))
    (g := fun n : Fin 3 → ℤ => ((1 + ‖fun i : Fin 3 => (n i : ℝ)‖) ^ 4)⁻¹)
    (fun n => inv_nonneg.mpr (by positivity)) (fun n => weight_le n) hmaj

end Work.BoseFixR.Rb5Lin
