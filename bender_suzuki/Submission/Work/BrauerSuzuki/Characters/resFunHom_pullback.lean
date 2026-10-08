import Mathlib
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.fdRep_simple_iff
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Characters

open Classical

/-- **Pullback of characters along a surjective homomorphism.**  If `φ : H →* K` is surjective,
then pulling back class functions along `φ` is injective on class functions, sends irreducible
characters of `K` to irreducible characters of `H`, and preserves the normalized inner product
`cfInner`.

(The irreducible case is a transport of representations: an `H`-invariant subspace of the
pullback of a simple `K`-module is `φ (H) = K`-invariant, hence everything.  The inner product
case is a counting argument: every value of `K` is attained `|ker φ|` times in `H`.) -/
theorem resFunHom_pullback {H K : Type*} [Group H] [Group K] [Fintype H] [Fintype K]
    (φ : H →* K) (hφ : Function.Surjective φ) :
    (∀ f : K → ℂ, Work.CharCore.IsClassFun f →
        Work.CharCore.IsClassFun (Work.Induction.resFunHom φ f)) ∧
    (∀ χ : K → ℂ, χ ∈ Work.CharCore.Irr K →
        Work.Induction.resFunHom φ χ ∈ Work.CharCore.Irr H) ∧
    (∀ f g : K → ℂ, Work.CharCore.cfInner (Work.Induction.resFunHom φ f)
        (Work.Induction.resFunHom φ g) = Work.CharCore.cfInner f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf g h
    simpa only [Work.Induction.resFunHom_apply, map_mul, map_inv] using hf (φ g) (φ h)
  · intro χ hχ
    obtain ⟨V, hV, hchar⟩ := (Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ
    let ρ' : Representation ℂ H ↥V := V.ρ.comp φ
    have hρ' : ∀ h : H, ρ' h = V.ρ (φ h) := fun h => rfl
    have hIrr : Representation.IsIrreducible V.ρ := (Work.CharCore.fdRep_simple_iff V).mp hV
    have hSO' : IsSimpleOrder (Subrepresentation ρ') := by
      let f : Subrepresentation V.ρ → Subrepresentation ρ' := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := fun h v hv => S.apply_mem_toSubmodule (φ h) hv }
      let g : Subrepresentation ρ' → Subrepresentation V.ρ := fun T =>
        { toSubmodule := T.toSubmodule
          apply_mem_toSubmodule := fun k v hv => by
            obtain ⟨h, rfl⟩ := hφ k
            exact T.apply_mem_toSubmodule h hv }
      have hfg : ∀ S, g (f S) = S := fun S => Subrepresentation.toSubmodule_injective rfl
      have hgf : ∀ T, f (g T) = T := fun T => Subrepresentation.toSubmodule_injective rfl
      have hbot : f ⊥ = (⊥ : Subrepresentation ρ') :=
        Subrepresentation.toSubmodule_injective rfl
      have htop : f ⊤ = (⊤ : Subrepresentation ρ') :=
        Subrepresentation.toSubmodule_injective rfl
      obtain ⟨a, b, hab⟩ := hIrr.exists_pair_ne
      have hne : f a ≠ f b := fun h => hab (by rw [← hfg a, ← hfg b, h])
      exact { toNontrivial := ⟨f a, f b, hne⟩
              eq_bot_or_eq_top := fun S => by
                rcases hIrr.eq_bot_or_eq_top (g S) with h | h
                · left; rw [← hgf S, h]; exact hbot
                · right; rw [← hgf S, h]; exact htop }
    refine (Work.CharCore.mem_Irr_iff_fdrep _).mpr ⟨FDRep.of ρ', ?_, ?_⟩
    · rw [Work.CharCore.fdRep_simple_iff, FDRep.of_ρ']
      exact hSO'
    · funext h
      simp only [FDRep.character, FDRep.of_ρ']
      rw [hρ' h, ← hchar]
      rfl
  · intro f g
    rw [Work.CharCore.cfInner_apply, Work.CharCore.cfInner_apply]
    simp only [Work.Induction.resFunHom_apply]
    -- enumerate `H` as `ker φ × K` to count the pullback sum
    let c : K → H := fun k => Classical.choose (hφ k)
    have hc : ∀ k : K, φ (c k) = k := fun k => Classical.choose_spec (hφ k)
    have hbij : Function.Bijective (fun p : φ.ker × K => (p.1 : H) * c p.2) := by
      constructor
      · rintro ⟨n1, k1⟩ ⟨n2, k2⟩ h
        have hk : k1 = k2 := by
          have h1 : φ ((n1 : H) * c k1) = φ ((n2 : H) * c k2) := congrArg φ h
          rw [map_mul, map_mul, MonoidHom.mem_ker.mp n1.2, MonoidHom.mem_ker.mp n2.2,
            one_mul, one_mul, hc k1, hc k2] at h1
          exact h1
        subst hk
        have hn : (n1 : H) = (n2 : H) := mul_right_cancel h
        exact Prod.ext (Subtype.ext hn) rfl
      · intro h
        refine ⟨(⟨h * (c (φ h))⁻¹, ?_⟩, φ h), ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
        · simp
    have key : (∑ p : φ.ker × K,
          f (φ ((p.1 : H) * c p.2)) * starRingEnd ℂ (g (φ ((p.1 : H) * c p.2))))
        = ∑ h : H, f (φ h) * starRingEnd ℂ (g (φ h)) :=
      Fintype.sum_bijective (fun p : φ.ker × K => (p.1 : H) * c p.2) hbij
        (fun p => f (φ ((p.1 : H) * c p.2)) * starRingEnd ℂ (g (φ ((p.1 : H) * c p.2))))
        (fun h => f (φ h) * starRingEnd ℂ (g (φ h))) (fun p => rfl)
    have hsum : (∑ h : H, f (φ h) * starRingEnd ℂ (g (φ h)))
        = (Fintype.card φ.ker : ℂ) * ∑ k : K, f k * starRingEnd ℂ (g k) := by
      rw [← key, Fintype.sum_prod_type]
      dsimp only
      have hinner : ∀ n : φ.ker,
          (∑ k : K, f (φ ((n : H) * c k)) * starRingEnd ℂ (g (φ ((n : H) * c k))))
            = ∑ k : K, f k * starRingEnd ℂ (g k) := by
        intro n
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_mul, MonoidHom.mem_ker.mp n.2, one_mul, hc]
      rw [Finset.sum_congr rfl (fun n _ => hinner n), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have hcardH : Fintype.card H = Fintype.card φ.ker * Fintype.card K := by
      rw [← Fintype.card_prod, ← Fintype.card_congr (Equiv.ofBijective _ hbij)]
    rw [hsum, hcardH, Nat.cast_mul, mul_inv_rev]
    have hker : (Fintype.card φ.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hK : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

end Work.BrauerSuzuki.Characters
