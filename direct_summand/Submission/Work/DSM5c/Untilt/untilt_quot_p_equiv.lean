import Mathlib
import Submission.Work.DSM5c.Untilt.Basic

/-!
# The mod-`p` reduction of the untilt

For `R` a perfect ring of characteristic `p` and `w ∈ R`, the untilt is
`untilt p R w = 𝕎 R ⧸ ([w] - p)`.  Writing `ξ := [w] - p`, this file proves

`(untilt p R w) ⧸ (p) ≃+* R ⧸ (w)`,

via the composite `𝕎 R → R ⧸ (w)` of the constant coefficient map, which has kernel exactly
`(ξ) ⊔ (p)`.

The endpoint is `Work.DSM5c.Untilt.untilt_quot_p_equiv`.
-/

namespace Work.DSM5c.Untilt

universe a

set_option linter.unusedSectionVars false

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]

/-- `[w] = ξ + p` in `𝕎 R`. -/
theorem teichmuller_eq_xi_add (w : R) :
    WittVector.teichmuller p w = xi p R w + (p : WittVector p R) := by
  rw [xi]
  abel

/-- The constant coefficient of a Teichmüller lift. -/
theorem constantCoeff_teichmuller (w : R) :
    WittVector.constantCoeff (WittVector.teichmuller p w) = w := by
  rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/-- In characteristic `p` the constant coefficient of `p` vanishes in `𝕎 R`. -/
theorem constantCoeff_p :
    WittVector.constantCoeff (p : WittVector p R) = 0 := by
  rw [map_natCast (WittVector.constantCoeff (p := p) (R := R)) p, CharP.cast_eq_zero R p]

/-- The ring homomorphism `𝕎 R → R ⧸ (w)` induced by the constant coefficient. -/
noncomputable def phi (w : R) : WittVector p R →+* R ⧸ Ideal.span {w} :=
  (Ideal.Quotient.mk (Ideal.span {w})).comp (WittVector.constantCoeff (p := p) (R := R))

@[simp]
theorem phi_apply (w : R) (x : WittVector p R) :
    phi w x = Ideal.Quotient.mk _ (WittVector.constantCoeff x) := rfl

theorem phi_surjective (w : R) : Function.Surjective (phi (p := p) (R := R) w) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := WittVector.constantCoeff_surjective p r
  exact ⟨x, by rw [phi_apply, hx, hr]⟩

/-- The key computation: the kernel of `𝕎 R → R ⧸ (w)` is `(ξ) ⊔ (p)`. -/
theorem ker_phi (w : R) :
    RingHom.ker (phi (p := p) (R := R) w) =
      Ideal.span {xi p R w} ⊔ Ideal.span {(p : WittVector p R)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, phi_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      dvd_def] at hx
    obtain ⟨s, hs⟩ := hx
    have hT : WittVector.teichmuller p (WittVector.constantCoeff x) =
        (xi p R w + (p : WittVector p R)) * WittVector.teichmuller p s := by
      rw [hs, map_mul, teichmuller_eq_xi_add]
    have h1 : x - WittVector.teichmuller p (WittVector.constantCoeff x) ∈
        Ideal.span {(p : WittVector p R)} := by
      rw [← WittVector.ker_constantCoeff (p := p) (k := R), RingHom.mem_ker, map_sub,
        constantCoeff_teichmuller, sub_self]
    have h2 : WittVector.teichmuller p (WittVector.constantCoeff x) ∈
        Ideal.span {xi p R w} ⊔ Ideal.span {(p : WittVector p R)} := by
      rw [hT, add_mul]
      exact add_mem
        (Ideal.mem_sup_left (Ideal.mul_mem_right _ _
          (Ideal.subset_span (Set.mem_singleton (xi p R w)))))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _
          (Ideal.subset_span (Set.mem_singleton (p : WittVector p R)))))
    rw [show x = (x - WittVector.teichmuller p (WittVector.constantCoeff x)) +
        WittVector.teichmuller p (WittVector.constantCoeff x) from (sub_add_cancel _ _).symm]
    exact add_mem (Ideal.mem_sup_right h1) h2
  · refine sup_le ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, phi_apply, constantCoeff_xi,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self w
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, phi_apply, constantCoeff_p,
        map_zero]

/-- The image of the ideal `(p) ⊆ 𝕎 R` in `𝕎 R ⧸ (ξ)` is the ideal `(p)` of the untilt. -/
theorem span_p_quotient_eq (w : R) :
    Ideal.span {(p : WittVector p R ⧸ Ideal.span {xi p R w})} =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {xi p R w})) (Ideal.span {(p : WittVector p R)}) := by
  have h : ((p : WittVector p R ⧸ Ideal.span {xi p R w})) =
      (Ideal.Quotient.mk (Ideal.span {xi p R w})) (p : WittVector p R) :=
    (map_natCast _ p).symm
  rw [h, Ideal.map_span, Set.image_singleton]

/-- The double quotient `(𝕎 R ⧸ (ξ)) ⧸ (p)` is `𝕎 R ⧸ ((ξ) ⊔ (p))`. -/
noncomputable def quotSupEquiv (w : R) :
    (WittVector p R ⧸ Ideal.span {xi p R w}) ⧸
        Ideal.span {(p : WittVector p R ⧸ Ideal.span {xi p R w})} ≃+*
      WittVector p R ⧸ (Ideal.span {xi p R w} ⊔ Ideal.span {(p : WittVector p R)}) :=
  (Ideal.quotEquivOfEq (span_p_quotient_eq (p := p) (R := R) w)).trans
    (DoubleQuot.quotQuotEquivQuotSup _ _)

@[simp]
theorem quotSupEquiv_mk (w : R) (x : WittVector p R) :
    quotSupEquiv w (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ x := by
  rw [quotSupEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk _ _ x

/-- **The mod-`p` reduction of the untilt**: `𝕎 R ⧸ ((ξ) ⊔ (p)) ≃+* R ⧸ (w)`, sending the class
of `x` to the class of `constantCoeff x`. -/
noncomputable def quotSupEquivR (w : R) :
    WittVector p R ⧸ (Ideal.span {xi p R w} ⊔ Ideal.span {(p : WittVector p R)}) ≃+*
      R ⧸ Ideal.span {w} :=
  (Ideal.quotEquivOfEq (ker_phi (p := p) (R := R) w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (phi_surjective (p := p) (R := R) w))

@[simp]
theorem quotSupEquivR_mk (w : R) (x : WittVector p R) :
    quotSupEquivR w (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (WittVector.constantCoeff x) := by
  rw [quotSupEquivR, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem untilt_quot_p_equiv (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p] (w : R) :
    ∃ e : (Work.DSM5c.untilt p R w ⧸ Ideal.span {(p : Work.DSM5c.untilt p R w)}) ≃+* (R ⧸ Ideal.span {w}),
      ∀ x : WittVector p R,
        e (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
          Ideal.Quotient.mk _ (WittVector.constantCoeff x) := by
  refine ⟨(quotSupEquiv (p := p) (R := R) w).trans (quotSupEquivR (p := p) (R := R) w), ?_⟩
  intro x
  simp

end Work.DSM5c.Untilt
