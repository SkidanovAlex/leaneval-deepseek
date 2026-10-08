import Mathlib
import Submission.Work.Frobenius.Induced.ConjChar
import Submission.Work.Frobenius.Induction.charPair_eq_finrank_intertwiningMap
import Submission.Work.Frobenius.Irr.charPair_irr_eq_ite
import Submission.Work.Frobenius.Irr.isIrr_one
import Submission.Work.RepTheory.span_range_eq_top_of_isIrreducible
import Submission.Work.RepTheory.eq_zero_of_trace_mul_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A fixed-point-free automorphism fixes no non-trivial irreducible character

For a normal subgroup `K ⊴ G` and an element `h : G` acting fixed-point-freely on `K`
(only the identity of `K` is fixed by conjugation by `h`), no non-trivial irreducible
character `θ ∈ Irr K` is fixed by `h`: `conjChar K h θ ≠ θ`.

The proof is the classical one.  Suppose `θ ∘ σ = θ`, where `σ : K ≃* K` is conjugation by
`h`, and let `ρ` be an irreducible representation with character `θ`.  Because
`ρ ∘ σ` and `ρ` have the same character, Schur orthogonality supplies a non-zero intertwiner
`B : ρ ⟶ ρ ∘ σ`, i.e. `B * ρ k = ρ (σ k) * B`.  Conjugating this relation by `ρ g` and taking
traces gives `trace (B * ρ (g * σ g⁻¹)) = trace B` for all `g`; since `g ↦ g * σ g⁻¹` is a
bijection of `K` (this is where fixed-point-freeness enters), we get `trace (B * ρ y) = trace B`
for all `y`, i.e. `trace ((ρ y - 1) * B) = 0`.

Now `∑_y (ρ y - 1) = -|K| • 1` (the sum of the matrices `ρ y` vanishes because `θ ≠ 1`), so
`1` lies in the span of the `ρ y - 1`; together with Burnside's theorem that the `ρ y`
(`span_range_eq_top_of_isIrreducible`) span the whole endomorphism algebra, the functional
`X ↦ trace (X * B)` vanishes on all of `End V`, so `B = 0` by non-degeneracy of the trace
form (`eq_zero_of_trace_mul_eq_zero`).  This contradicts `B ≠ 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open Classical
open Work.Frobenius

namespace Work.Frobenius.Induced

/-- The sum of the matrices of an irreducible representation with non-trivial character is
zero: `∑_g ρ g = 0`.  The sum is a self-intertwiner, hence a scalar `c • 1` by Schur's
lemma; its trace is `∑_g χ(g) = |G| ⟨χ, 1⟩ = 0` because `χ ≠ 1`, and `c * dim = 0`. -/
theorem sum_representation_eq_zero {G : Type*} [Group G] [Fintype G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (h : ρ.character ≠ 1) :
    ∑ g : G, (ρ g : V →ₗ[ℂ] V) = 0 := by
  classical
  -- `S = ∑_g ρ g` commutes with every `ρ x`
  have hcomm : ∀ x : G, (∑ g : G, (ρ g : V →ₗ[ℂ] V)) * ρ x
      = ρ x * (∑ g : G, (ρ g : V →ₗ[ℂ] V)) := by
    intro x
    have hl : (∑ g : G, (ρ g : V →ₗ[ℂ] V)) * ρ x = ∑ g : G, (ρ g : V →ₗ[ℂ] V) := by
      rw [Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun g _ => (map_mul ρ g x).symm)]
      exact Equiv.sum_comp (Equiv.mulRight x) (fun g => (ρ g : V →ₗ[ℂ] V))
    have hr : ρ x * (∑ g : G, (ρ g : V →ₗ[ℂ] V)) = ∑ g : G, (ρ g : V →ₗ[ℂ] V) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun g _ => (map_mul ρ x g).symm)]
      exact Equiv.sum_comp (Equiv.mulLeft x) (fun g => (ρ g : V →ₗ[ℂ] V))
    rw [hl, hr]
  -- package `S` as a self-intertwiner
  let Sint : ρ.IntertwiningMap ρ :=
    { toLinearMap := ∑ g : G, (ρ g : V →ₗ[ℂ] V)
      isIntertwining' := fun x => by
        ext v
        simp only [LinearMap.comp_apply]
        have h3 := congrArg (fun f : V →ₗ[ℂ] V => f v) (hcomm x)
        simpa only [Module.End.mul_apply] using h3 }
  -- Schur: every self-intertwiner is a scalar
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 Sint
  have hcL : (∑ g : G, (ρ g : V →ₗ[ℂ] V)) = c • (1 : V →ₗ[ℂ] V) := by
    have h2 := congrArg (fun f : ρ.IntertwiningMap ρ => f.toLinearMap) hc
    show Sint.toLinearMap = c • (1 : V →ₗ[ℂ] V)
    rw [← h2]
    ext v
    simp [Representation.IntertwiningMap.algebraMap_apply]
  -- traces
  have htr : LinearMap.trace ℂ V (∑ g : G, (ρ g : V →ₗ[ℂ] V))
      = c * (Module.finrank ℂ V : ℂ) := by
    rw [hcL, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hchar : ∑ g : G, ρ.character g = 0 := by
    have hχ : ρ.character ∈ Irr G := ⟨{ V := V, ρ := ρ, irred := ‹ρ.IsIrreducible› }, rfl⟩
    have hpair := Work.Frobenius.Irr.charPair_irr_eq_ite (G := G) hχ
      (Work.Frobenius.Irr.isIrr_one (G := G))
    rw [if_neg h] at hpair
    rw [charPair_apply] at hpair
    simp only [Pi.one_apply, mul_one] at hpair
    have hcard : (Nat.card G : ℂ) ≠ 0 := by
      have := Nat.card_pos (α := G); exact_mod_cast this.ne'
    exact (mul_eq_zero.mp hpair).resolve_left (inv_ne_zero hcard)
  have htrl : LinearMap.trace ℂ V (∑ g : G, (ρ g : V →ₗ[ℂ] V)) = 0 := by
    rw [map_sum]
    simpa only [Representation.character] using hchar
  haveI hnt : Nontrivial V := by
    haveI := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp ‹ρ.IsIrreducible›
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have : 0 < Module.finrank ℂ V := Module.finrank_pos
    exact_mod_cast this.ne'
  have hc0 : c = 0 := (mul_eq_zero.mp (htr ▸ htrl)).resolve_right hd
  rw [hcL, hc0, zero_smul]

theorem conjChar_ne_self_of_fpf {G : Type*} [Group G] [Fintype G] {K : Subgroup G} [K.Normal]
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθ1 : θ ≠ 1) {h : G}
    (hfpf : ∀ k : G, k ∈ K → h * k * h⁻¹ = k → k = 1) :
    conjChar K h θ ≠ θ := by
  intro hconj
  have hKn : K.Normal := inferInstance
  -- conjugation by `h` as an endomorphism of `K`
  let σ : K →* K :=
    { toFun := fun k => ⟨h * (k : G) * h⁻¹, hKn.conj_mem (k : G) k.2 h⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hconjChar : conjChar K h θ = fun k => θ (σ k) := by
    funext k
    rw [conjChar_apply]
    rfl
  have hstab : ∀ k : K, θ (σ k) = θ k := by
    intro k
    have := congrFun hconj k
    rw [hconjChar] at this
    exact this
  have hfpf' : ∀ x : K, σ x = x → x = 1 := by
    intro x hx
    apply Subtype.ext
    exact hfpf (x : G) x.2 (by
      have := congrArg Subtype.val hx
      show h * (x : G) * h⁻¹ = (x : G)
      simpa [σ] using this)
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
    rw [show LinearMap.trace ℂ d.V (d.ρ (σ k)) = θ (σ k) from congrFun hd' (σ k), hstab k]
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
    have h2 := hfpf' (b⁻¹ * a) h1.symm
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
