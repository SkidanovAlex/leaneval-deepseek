import Mathlib
import Submission.Work.CharPrelim.weightSpace_defs
import Submission.Work.CharPrelim.weightSpace_indep
import Submission.Work.CharPrelim.weightSpace_span_of_primitiveRoot
import Submission.Work.Hering.AppVII.conjNormal_char_ne

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The orbit-sum lemma for Appendix VII

Let `H` be a finite group with subgroups `P, Q` such that `Q` is abelian and normal, `P ∩ Q = 1`,
`P Q = H`, `|P|` is prime and `⁅P, Q⁆ = Q`.  Let `M` be a finite-dimensional `F`-vector space on
which `H` acts (`F` a field containing a primitive `|Q|`-th root of unity, with `|Q|` invertible in
`F`).  If `Q` has no nonzero fixed point in `M` and `M ≠ 0`, then `P` has a nonzero fixed point.

The proof is the classical "orbit sum" argument.  Since `F` contains a primitive `|Q|`-th root of
unity and `|Q|` is invertible, every irreducible representation of the finite abelian group `Q` over
`F` is one-dimensional, and

`M = ⨁_{χ : Q →* Fˣ} M_χ`,  `M_χ = {v | ∀ q, ρ q v = χ q • v}`

(`Work.CharPrelim.weightSpace_span_of_primitiveRoot` for the spanning,
`Work.CharPrelim.weightSpace_indep` for the independence).  The hypothesis `M^Q = 0` says that the
weight space of the trivial character is zero, so some `χ ≠ 1` has `M_χ ≠ 0`; pick `0 ≠ v ∈ M_χ`.

Now `[P,Q] = Q` forces the orbit of `χ` under the conjugation action of `P` to have size `|P|`
(`Work.Hering.AppVII.conjNormal_char_ne`): if `p ∈ P` fixes `χ` then `χ` kills all commutators
`⁅p, q⁆`, and since `|P|` is prime every element of `P` is a power of `p`, so that `χ` kills
`⁅P,Q⁆ = Q`.  Hence the `ρ p v`, `p ∈ P`, lie in *distinct* weight spaces, and the orbit sum

`u = ∑_{p ∈ P} ρ p v`

is nonzero: applying the character projector of the class of `χ` isolates `v ≠ 0`.  Finally `u` is
fixed by `P` because `P` is a group.
-/

namespace Work.Hering.AppVII

theorem orbit_sum {F M H : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] [Group H] [Finite H]
    (ρ : Representation F H M) (Q P : Subgroup H) (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤)
    (hQa : IsMulCommutative ↥Q) (hpc : (Nat.card ↥P).Prime) (hcomm : ⁅P, Q⁆ = Q)
    (hroot : ∃ ζ : F, IsPrimitiveRoot ζ (Nat.card ↥Q))
    (hcharQ : IsUnit ((Nat.card ↥Q : ℕ) : F))
    (hfixQ : ∀ v : M, (∀ q ∈ Q, ρ q v = v) → v = 0) (hne : Nontrivial M) :
    ∃ v : M, v ≠ 0 ∧ ∀ p ∈ P, ρ p v = v := by
  classical
  haveI hNorm : Q.Normal := hQn
  haveI hNtriv : Nontrivial M := hne
  letI : CommGroup ↥Q := { (inferInstance : Group ↥Q) with
    mul_comm := fun a b => hQa.is_comm.comm a b }
  letI : Fintype ↥Q := Fintype.ofFinite ↥Q
  letI : Fintype ↥P := Fintype.ofFinite ↥P
  let τ : ↥Q →* Module.End F M := ρ.comp Q.subtype
  obtain ⟨ζ, hζ⟩ := hroot
  have hspan : (⨆ χ : ↥Q →* Fˣ, Work.CharPrelim.weightSpace τ χ) = ⊤ :=
    Work.CharPrelim.weightSpace_span_of_primitiveRoot τ hcharQ ⟨ζ, hζ⟩
  -- the weight space of the trivial character is the fixed-point space of `Q`
  have htriv : Work.CharPrelim.weightSpace τ (1 : ↥Q →* Fˣ) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    refine hfixQ v (fun q hq => ?_)
    have h := (Work.CharPrelim.mem_weightSpace τ 1 v).mp hv ⟨q, hq⟩
    simpa [τ] using h
  have hne_top : (⊤ : Submodule F M) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hx' : x ∈ (⊥ : Submodule F M) := by rw [← h]; trivial
    rw [Submodule.mem_bot] at hx'
    exact hx hx'
  -- some nontrivial character has a nonzero weight space
  have hex : ∃ χ : ↥Q →* Fˣ, χ ≠ 1 ∧ Work.CharPrelim.weightSpace τ χ ≠ ⊥ := by
    by_contra hcon
    have hall : ∀ χ : ↥Q →* Fˣ, Work.CharPrelim.weightSpace τ χ = ⊥ := by
      intro χ
      by_cases hχ : χ = 1
      · rw [hχ]; exact htriv
      · by_contra hW
        exact hcon ⟨χ, hχ, hW⟩
    have : (⨆ χ : ↥Q →* Fˣ, Work.CharPrelim.weightSpace τ χ) = ⊥ := by
      rw [iSup_eq_bot]
      exact hall
    rw [this] at hspan
    exact hne_top hspan.symm
  obtain ⟨χ, hχ1, hWne⟩ := hex
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff _).mp hWne
  -- the conjugation action of `H` on `↥Q` and the conjugate characters
  let σ : H →* MulAut ↥Q := MulAut.conjNormal
  let ψ : ↥P → (↥Q →* Fˣ) := fun p => χ.comp ((σ (p : H))⁻¹).toMonoidHom
  have hψ1 : ψ (1 : ↥P) = χ := by
    ext q
    simp [ψ, σ]
  have hcoe : ∀ (p p' : ↥P) (q : ↥Q),
      (σ (p : H))⁻¹ (σ (p' : H) q) = σ (((p⁻¹ * p' : ↥P)) : H) q := by
    intro p p' q
    rw [← map_inv, ← MulAut.mul_apply, ← map_mul]
    rfl
  have hcoe' : ∀ (p : ↥P) (q : ↥Q), (σ (p : H))⁻¹ (σ (p : H) q) = q := by
    intro p q
    rw [← MulAut.mul_apply, ← map_inv, ← map_mul, inv_mul_cancel, map_one]
    rfl
  -- the conjugate characters of the orbit of `χ` under `P` are pairwise distinct
  have hdist : ∀ p p' : ↥P, ψ p = ψ p' → p = p' := by
    intro p p' hp
    have h2 : χ.comp (σ (((p⁻¹ * p' : ↥P)) : H)).toMonoidHom = χ := by
      ext q
      have h := MonoidHom.ext_iff.mp hp (σ (p' : H) q)
      change χ ((σ (p : H))⁻¹ (σ (p' : H) q)) = χ ((σ (p' : H))⁻¹ (σ (p' : H) q)) at h
      rw [hcoe p p' q, hcoe' p' q] at h
      exact congrArg (fun u : Fˣ => (u : F)) h
    have h3 : p⁻¹ * p' = 1 := by
      by_contra hne1
      exact conjNormal_char_ne P Q hcomm hpc hχ1 hne1 h2
    exact inv_mul_eq_one.mp h3
  -- each `ρ p v` lies in the weight space of the conjugate character `ψ p`
  have hmem : ∀ p : ↥P, ρ (p : H) v ∈ Work.CharPrelim.weightSpace τ (ψ p) := by
    intro p
    rw [Work.CharPrelim.mem_weightSpace]
    intro q
    have hconj : (q : H) * (p : H) = (p : H) * (((σ (p : H))⁻¹ q : ↥Q) : H) := by
      rw [MulAut.conjNormal_inv_apply]
      group
    have hq : τ q = (ρ (q : H) : Module.End F M) := rfl
    rw [hq, ← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
    rw [show ρ (((σ (p : H))⁻¹ q : ↥Q) : H) = τ ((σ (p : H))⁻¹ q) from rfl]
    rw [(Work.CharPrelim.mem_weightSpace τ χ v).mp hvW ((σ (p : H))⁻¹ q)]
    rw [LinearMap.map_smul]
    rfl
  -- the orbit sum
  refine ⟨∑ p : ↥P, ρ (p : H) v, ?_, ?_⟩
  · -- nonzero: apply the character projection
    intro hzero
    have h1 : Work.CharPrelim.charProj τ χ (∑ p : ↥P, ρ (p : H) v) = 0 := by
      rw [hzero, map_zero]
    have h2 : Work.CharPrelim.charProj τ χ (∑ p : ↥P, ρ (p : H) v)
        = ∑ p : ↥P, Work.CharPrelim.charProj τ χ (ρ (p : H) v) := by
      rw [map_sum]
    rw [h2] at h1
    have hvanish : ∀ p ∈ (Finset.univ : Finset ↥P), p ≠ 1 →
        Work.CharPrelim.charProj τ χ (ρ (p : H) v) = 0 := fun p _ hp =>
      Work.CharPrelim.charProj_apply_of_mem_ne τ
        (fun h => hp (hdist p 1 (h.symm.trans hψ1.symm))) (hmem p)
    have h3 : (∑ p : ↥P, Work.CharPrelim.charProj τ χ (ρ (p : H) v)) = v := by
      rw [Finset.sum_eq_single_of_mem (1 : ↥P) (Finset.mem_univ 1) hvanish]
      have hpt : ρ (((1 : ↥P)) : H) v = v := by
        rw [show (((1 : ↥P)) : H) = (1 : H) from rfl, map_one, Module.End.one_apply]
      rw [hpt]
      exact Work.CharPrelim.charProj_apply_of_mem τ χ hcharQ hvW
    rw [h3] at h1
    exact hv0 h1
  · -- the orbit sum is `P`-fixed
    intro g hg
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : ↥P))
      (fun p : ↥P => ρ g (ρ (p : H) v)) (fun p : ↥P => ρ (p : H) v) (fun p => ?_)
    rw [← Module.End.mul_apply, ← map_mul]
    rfl

end Work.Hering.AppVII
