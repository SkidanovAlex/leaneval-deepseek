import Mathlib
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Defs

namespace Work.Engulf.E4Aux

open Set Metric PL

/-- **The prism push step (`E4d`, Newman §14, Theorem 2 in chart coordinates)**.  Transport of `Work.Engulf.PrismPushRelForm` along the affine equivalence `T : E n ≃ᵃ ℝ Pr (n-q-1) q` produced by G2: given that the floor `{t = γ₀ z}` and the region over `J` are inside `U`, the whole prism sits in `W`, and the closed set `A` meets the prism only in the floor and over `J`, there is a self-homeomorphism `h` of `E n`, compactly supported inside `W`, fixing `A`, and carrying the whole prism into `h '' U`. -/
theorem prism_push_step {n q : ℕ} (hq : q + 1 ≤ n)
    (T : PL.E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q)
    (F J : Set (PL.E q)) (hF : IsCompact F) (hJc : IsClosed J) (hJF : J ⊆ F)
    (γ₀ γ₁ : PL.E q → ℝ) (hγ₀ : Continuous γ₀) (hγ₁ : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z) (hfr : ∀ z ∈ frontier F, γ₀ z = γ₁ z)
    (U W A : Set (PL.E n)) (hU : IsOpen U) (hW : IsOpen W) (hAc : IsClosed A) (hAU : A ⊆ U)
    (hb : ∀ z ∈ F, ((0 : PL.E (n - q - 1)), z, γ₀ z) ∈ T '' U)
    (hJ : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E (n - q - 1)), z, t) ∈ T '' U)
    (hW' : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E (n - q - 1)), z, t) ∈ T '' W)
    (hAs : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E (n - q - 1)), z, t) ∈ T '' A →
        t = γ₀ z ∨ z ∈ J)
    (push : Work.Engulf.PrismPushRelForm) :
    ∃ h : PL.E n ≃ₜ PL.E n, PL.CSupp h W ∧ (∀ x ∈ A, h x = x) ∧
      ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        (T.symm ((0 : PL.E (n - q - 1)), z, t)) ∈ h '' U := by
  classical
  -- `T` as a homeomorphism; its coercion is definitionally `T` itself.
  let e : PL.E n ≃ₜ Work.Engulf.Pr (n - q - 1) q :=
    (AffineEquiv.toContinuousAffineEquiv T).toHomeomorph
  have he : ⇑e = ⇑T := rfl
  have hes : ⇑e.symm = ⇑T.symm := rfl
  -- The relative prism push, applied to the transported open sets `T '' U`, `T '' W` and the
  -- transported closed set `T '' A`.
  obtain ⟨h', h'supp, h'fix, h'car⟩ :=
    push F J hF hJc hJF γ₀ γ₁ hγ₀ hγ₁ hle hfr (T '' U) (T '' W) (T '' A)
      (e.isOpenMap U hU) (e.isOpenMap W hW) (e.isClosedMap A hAc)
      (fun x ⟨a, ha, hax⟩ => ⟨a, hAU ha, hax⟩) hb hJ hW' hAs
  -- Transport `h'` back along `T`; the support shrinks to `T.symm '' C'`.
  refine ⟨(e.trans h').trans e.symm, ?_, ?_, ?_⟩
  · obtain ⟨C', hC'c, hC'sub, hC'fix⟩ := h'supp
    refine ⟨e.symm '' C', hC'c.image e.symm.continuous, ?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨w, hw, hwy⟩ := hC'sub hy
      rw [← hwy, ← he]
      simpa using hw
    · intro x hx
      simp only [Homeomorph.trans_apply]
      have hx' : e x ∉ C' := fun h => hx ⟨e x, h, by simp⟩
      rw [hC'fix (e x) hx']
      exact e.symm_apply_apply x
  · intro x hx
    simp only [Homeomorph.trans_apply]
    rw [h'fix (e x) ⟨x, hx, rfl⟩]
    exact e.symm_apply_apply x
  · intro z hz t ht
    obtain ⟨y, hy, hy'⟩ := h'car z hz t ht
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨u, hu, ?_⟩
    simp only [Homeomorph.trans_apply]
    rw [he, hy', hes]

end Work.Engulf.E4Aux
