import Mathlib
import Submission.Work.Frobenius.Induced.conjChar_ne_self_of_fpf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A fixed-point-free endomorphism fixes no non-trivial irreducible character

Let `K` be a finite group and `σ : K →* K` an endomorphism all of whose fixed points are
trivial (`σ x = x → x = 1`).  Then the only irreducible complex character of `K` that is
fixed by `σ` (`θ (σ x) = θ x` for all `x`) is the trivial character:

`irr_eq_one_of_fpf : θ ∈ Irr K → (∀ x, θ (σ x) = θ x) → θ = 1`.

The proof is the same argument as for `conjChar_ne_self_of_fpf`, but with the fixed-point-free
automorphism given directly instead of being induced by conjugation in an ambient group.
Suppose `θ ≠ 1` and let `ρ` be an irreducible representation with character `θ`.  The
representation `ρ ∘ σ` has the same character as `ρ`, so Schur orthogonality supplies a
non-zero intertwiner `B : ρ ⟶ ρ ∘ σ`, i.e. `B * ρ k = ρ (σ k) * B`.  Conjugating this relation
by `ρ g` and taking traces gives `trace (B * ρ (g * σ g⁻¹)) = trace B` for all `g`; since
`g ↦ g * σ g⁻¹` is a bijection of `K` (fixed-point-freeness), we get
`trace (B * ρ y) = trace B` for all `y`, i.e. `trace ((ρ y - 1) * B) = 0`.

Now `∑_y (ρ y - 1) = -|K| • 1` (the sum of the matrices `ρ y` vanishes because `θ ≠ 1`), so `1`
lies in the span of the `ρ y - 1`; together with Burnside's theorem that the `ρ y` span the whole
endomorphism algebra (`span_range_eq_top_of_isIrreducible`), the functional
`X ↦ trace (X * B)` vanishes on all of `End V`, so `B = 0` by non-degeneracy of the trace form
(`eq_zero_of_trace_mul_eq_zero`).  This contradicts `B ≠ 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open Classical
open Work.Frobenius

namespace Work.Frobenius.Induced

/-- **A fixed-point-free endomorphism fixes no non-trivial irreducible character.**  If `σ` is
an endomorphism of a finite group `K` whose only fixed point is `1`, then every irreducible
character of `K` fixed by `σ` is the trivial character. -/
theorem irr_eq_one_of_fpf {K : Type} [Group K] [Fintype K] (σ : K →* K)
    (hfpf : ∀ x : K, σ x = x → x = 1) {θ : K → ℂ} (hθ : θ ∈ Work.Frobenius.Irr K)
    (hfix : ∀ x : K, θ (σ x) = θ x) : θ = fun _ : K => 1 := by
  classical
  by_contra hθ1
  -- an irreducible representation affording `θ`
  obtain ⟨d, hd⟩ := hθ
  have hd' : d.ρ.character = θ := hd
  haveI : d.ρ.IsIrreducible := d.irred
  let ρσ : Representation ℂ K d.V := d.ρ.comp σ
  have hρσchar : ρσ.character = d.ρ.character := by
    funext k
    have h1 : ρσ k = d.ρ (σ k) := MonoidHom.comp_apply d.ρ σ k
    show LinearMap.trace ℂ d.V (ρσ k) = LinearMap.trace ℂ d.V (d.ρ k)
    rw [h1]
    rw [show LinearMap.trace ℂ d.V (d.ρ (σ k)) = θ (σ k) from congrFun hd' (σ k), hfix k]
    exact (congrFun hd' k).symm
  -- the pairing of `ρ` with `ρ ∘ σ` is `1`, so a non-zero intertwiner exists
  have hpair : charPair ρσ.character (d.ρ.character) = 1 := by
    rw [hρσchar]
    rw [Work.Frobenius.Irr.charPair_irr_eq_ite (G := K) ⟨d, rfl⟩ ⟨d, rfl⟩]
    simp
  have hfin : Module.finrank ℂ (d.ρ.IntertwiningMap ρσ) = 1 := by
    have := Work.Frobenius.Induction.charPair_eq_finrank_intertwiningMap d.ρ ρσ
    rw [hpair] at this
    exact_mod_cast this.symm
  haveI : Nontrivial (d.ρ.IntertwiningMap ρσ) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : Module.finrank ℂ (d.ρ.IntertwiningMap ρσ) = 0 :=
      Module.finrank_eq_zero_of_subsingleton ℂ _
    omega
  obtain ⟨B, hBne⟩ := exists_ne (0 : d.ρ.IntertwiningMap ρσ)
  let Bl : d.V →ₗ[ℂ] d.V := B.toLinearMap
  have hBlne : Bl ≠ 0 := by
    intro h
    exact hBne (Representation.IntertwiningMap.toLinearMap_injective d.ρ ρσ
      (by simpa [Bl] using h))
  have hB : ∀ k : K, Bl * d.ρ k = d.ρ (σ k) * Bl := by
    intro k
    ext v
    have hh := Representation.IntertwiningMap.isIntertwining d.ρ ρσ B k v
    simpa [Bl, ρσ, MonoidHom.comp_apply] using hh
  -- traces: `trace (Bl * ρ (g σ g⁻¹)) = trace Bl`
  have htrace : ∀ g : K, LinearMap.trace ℂ d.V (d.ρ (g * (σ g)⁻¹) * Bl)
      = LinearMap.trace ℂ d.V Bl := by
    intro g
    have hconj : d.ρ g * Bl * d.ρ (g⁻¹) = d.ρ (g * (σ g)⁻¹) * Bl := by
      rw [mul_assoc, hB (g⁻¹), ← mul_assoc, ← map_mul, map_inv]
    have htrL : LinearMap.trace ℂ d.V (d.ρ g * Bl * d.ρ (g⁻¹))
        = LinearMap.trace ℂ d.V Bl := by
      rw [mul_assoc, LinearMap.trace_mul_comm ℂ (d.ρ g) (Bl * d.ρ (g⁻¹)),
        mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact (congrArg (LinearMap.trace ℂ d.V) hconj).symm.trans htrL
  -- `g ↦ g * σ g⁻¹` is a bijection of `K`
  have hsurj : Function.Surjective (fun g : K => g * (σ g)⁻¹) := by
    refine Finite.surjective_of_injective ?_
    intro a b hab
    have hab' : a * (σ a)⁻¹ = b * (σ b)⁻¹ := hab
    have key : b⁻¹ * a * (σ a)⁻¹ = (σ b)⁻¹ := by
      calc b⁻¹ * a * (σ a)⁻¹
          = b⁻¹ * (a * (σ a)⁻¹) := by rw [mul_assoc]
        _ = b⁻¹ * (b * (σ b)⁻¹) := by rw [hab']
        _ = (σ b)⁻¹ := by group
    have h1 : b⁻¹ * a = σ (b⁻¹ * a) := by
      calc b⁻¹ * a = b⁻¹ * a * ((σ a)⁻¹ * σ a) := by group
        _ = (b⁻¹ * a * (σ a)⁻¹) * σ a := by group
        _ = (σ b)⁻¹ * σ a := by rw [key]
        _ = σ (b⁻¹ * a) := by rw [← map_inv, ← map_mul]
    have h2 := hfpf (b⁻¹ * a) h1.symm
    exact (inv_mul_eq_one.mp h2).symm
  have htrace_all : ∀ y : K, LinearMap.trace ℂ d.V (d.ρ y * Bl)
      = LinearMap.trace ℂ d.V Bl := by
    intro y
    obtain ⟨g, rfl⟩ := hsurj y
    exact htrace g
  have htr0 : ∀ y : K, LinearMap.trace ℂ d.V ((d.ρ y - 1) * Bl) = 0 := by
    intro y
    rw [sub_mul, one_mul, map_sub, htrace_all y, sub_self]
  -- Burnside and the vanishing sum
  have hBurn : Submodule.span ℂ (Set.range (fun g : K => (d.ρ g : d.V →ₗ[ℂ] d.V))) = ⊤ :=
    Work.RepTheory.span_range_eq_top_of_isIrreducible d.ρ
  have hsum0 : ∑ g : K, (d.ρ g : d.V →ₗ[ℂ] d.V) = 0 :=
    sum_representation_eq_zero d.ρ (by rw [hd']; exact hθ1)
  let W : Submodule ℂ (d.V →ₗ[ℂ] d.V) :=
    Submodule.span ℂ (Set.range (fun y : K => ((d.ρ y - 1 : d.V →ₗ[ℂ] d.V))))
  have h1mem : (1 : d.V →ₗ[ℂ] d.V) ∈ W := by
    have hsum1 : (∑ y : K, (d.ρ y - 1)) = - (Nat.card K : ℂ) • (1 : d.V →ₗ[ℂ] d.V) := by
      rw [Finset.sum_sub_distrib, hsum0, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, zero_sub, ← neg_smul]
    have hmem : (∑ y : K, (d.ρ y - 1)) ∈ W :=
      Submodule.sum_mem _ (fun y _ => Submodule.subset_span ⟨y, rfl⟩)
    rw [hsum1] at hmem
    have hne : (Nat.card K : ℂ) ≠ 0 := by
      have := Nat.card_pos (α := K); exact_mod_cast this.ne'
    have hsm := Submodule.smul_mem W ((-(Nat.card K : ℂ))⁻¹) hmem
    rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hne), one_smul] at hsm
    exact hsm
  have hWtop : W = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hBurn, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    change (d.ρ y : d.V →ₗ[ℂ] d.V) ∈ W
    rw [← sub_add_cancel (d.ρ y) (1 : d.V →ₗ[ℂ] d.V)]
    exact Submodule.add_mem W (Submodule.subset_span ⟨y, rfl⟩) h1mem
  have hzero : ∀ X : d.V →ₗ[ℂ] d.V, LinearMap.trace ℂ d.V (X * Bl) = 0 := by
    intro X
    have key : W ≤ LinearMap.ker ((LinearMap.trace ℂ d.V).comp (LinearMap.mulRight ℂ Bl)) := by
      rw [Submodule.span_le]
      rintro z ⟨y, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
      exact htr0 y
    exact key (by rw [hWtop]; exact Submodule.mem_top)
  exact hBlne (Work.RepTheory.eq_zero_of_trace_mul_eq_zero hzero)

end Work.Frobenius.Induced
