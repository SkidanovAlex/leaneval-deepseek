import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.NeTwoIsIntegralMap
import Submission.Work.MotC2.NeTwoDecomp
import Submission.Work.MotC2.CharTwoNormCrux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

/-- Normality of the affine coordinate ring in characteristic two: `affRing E = L[x,y]` is
integrally closed in `L(E)`.

The argument is the characteristic-two trace/norm argument.  Let `h ∈ L(E)` be integral over
`R = L[x,y]`, write `h = p + q·y` with `p, q ∈ L(x)` (`NeTwoDecomp`), and let `σ = negAlgEquiv E`
be the conjugation `x ↦ x`, `y ↦ -y - e`; since `char L = 2`, `σ y = y + e` and

  `h + σ h = q·e`,   `h · σ h = p ^ 2 + p·q·e + q ^ 2·c`,

with `e = eK E = a₁x + a₃` and `c = cK E = x³ + a₂x² + a₄x + a₆`.  Both `h + σh` and `h·σh` are
integral over `L[x] = Ax E` (they are sums/products of `h` and `σh`, and `σ` preserves `L[x]`),
and they lie in `L(x) = range (xPsi E)`; since `L[x]` is integrally closed in `L(x)`
(`IsIntegrallyClosed (Polynomial L)`, via
`NeTwoSetup.mem_Ax_of_isIntegral_of_mem_range_xPsi`) they lie in `Ax E`.  Then `CharTwoNormCrux`
gives `p, q ∈ L[x]`, whence `h = p + q·y ∈ R`. -/
theorem AffRingNormalCharTwo (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) = 0) :
    IsIntegrallyClosedIn ↥((Work.MotC2.affRing E).toSubring) (Work.MotC2.Func E) := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro h hh
  -- Step 0: `h` and its conjugate are integral over `L[x]`.
  have hhAx : IsIntegral ↥(Ax E) h := isIntegral_Ax_of_isIntegral_affRing E hh
  have hσhAx : IsIntegral ↥(Ax E) (negAlgEquiv E h) :=
    NeTwoIsIntegralMap (negAlgEquiv E).toRingEquiv.toRingHom (RingHom.id ↥(Ax E))
      (fun r => by
        simp only [RingHom.id_apply]
        exact negAlgEquiv_mem_Ax E r.2)
      hhAx
  have hTAx : IsIntegral ↥(Ax E) (h + negAlgEquiv E h) := hhAx.add hσhAx
  have hNAx : IsIntegral ↥(Ax E) (h * negAlgEquiv E h) := hhAx.mul hσhAx
  -- Step 1: decompose `h` in the `L[x]`-basis `{1, y}` of `L(E)`.
  obtain ⟨b₁, b₂, s₁, s₂, hb₁, hb₂, hs₁, hs₂, _hden, hdecomp, hN₂ne, hident⟩ :=
    NeTwoDecomp L E h
  set N₂ : Func E := s₁ ^ 2 - s₁ * s₂ * eK E - s₂ ^ 2 * cK E with hN₂def
  set u₁ : Func E := b₁ * s₁ - b₁ * s₂ * eK E - b₂ * s₂ * cK E with hu₁def
  set u₂ : Func E := b₂ * s₁ - b₁ * s₂ with hu₂def
  have hN₂Ax : N₂ ∈ Ax E := by
    rw [hN₂def]
    exact sub_mem (sub_mem (pow_mem hs₁ 2) (mul_mem (mul_mem hs₁ hs₂) (eK_mem E)))
      (mul_mem (pow_mem hs₂ 2) (cK_mem E))
  have hu₁Ax : u₁ ∈ Ax E := by
    rw [hu₁def]
    exact sub_mem (sub_mem (mul_mem hb₁ hs₁) (mul_mem (mul_mem hb₁ hs₂) (eK_mem E)))
      (mul_mem (mul_mem hb₂ hs₂) (cK_mem E))
  have hu₂Ax : u₂ ∈ Ax E := by
    rw [hu₂def]
    exact sub_mem (mul_mem hb₂ hs₁) (mul_mem hb₁ hs₂)
  have hp : u₁ / N₂ ∈ Set.range (xPsi E) :=
    mem_range_xPsi_of_mul E hu₁Ax hN₂Ax hN₂ne (by rw [div_mul_cancel₀ _ hN₂ne])
  have hq : u₂ / N₂ ∈ Set.range (xPsi E) :=
    mem_range_xPsi_of_mul E hu₂Ax hN₂Ax hN₂ne (by rw [div_mul_cancel₀ _ hN₂ne])
  have hh_eq : h = u₁ / N₂ + (u₂ / N₂) * genY E := by
    have h1 : u₁ / N₂ + (u₂ / N₂) * genY E = (u₁ + u₂ * genY E) / N₂ := by
      rw [div_mul_eq_mul_div, ← add_div]
    rw [h1, eq_div_iff hN₂ne]
    exact hident
  -- Step 2: the characteristic-two trace and norm identities.
  have hσp : negAlgEquiv E (u₁ / N₂) = u₁ / N₂ := negAlgEquiv_mem_range_xPsi E hp
  have hσq : negAlgEquiv E (u₂ / N₂) = u₂ / N₂ := negAlgEquiv_mem_range_xPsi E hq
  have hσh_eq : negAlgEquiv E h =
      u₁ / N₂ - (u₂ / N₂) * eK E - (u₂ / N₂) * genY E := by
    rw [hh_eq, map_add, map_mul, hσp, hσq, negAlgEquiv_genY']
    first | refl_ring1 | ring
  have hT_eq : h + negAlgEquiv E h = 2 * (u₁ / N₂) - (u₂ / N₂) * eK E := by
    rw [hσh_eq, hh_eq]
    first | refl_ring1 | ring
  have hNm_eq : h * negAlgEquiv E h =
      (u₁ / N₂) ^ 2 - (u₁ / N₂) * (u₂ / N₂) * eK E - (u₂ / N₂) ^ 2 * cK E := by
    rw [hσh_eq, hh_eq]
    linear_combination (norm := first | refl_ring1 | ring1) (-((u₂ / N₂) ^ 2)) * (y_sq E)
  -- Step 3: in characteristic two `-z = z` and `2 = 0`, so the trace is `q·e` and the norm is
  -- `p ^ 2 + p·q·e + q ^ 2·c`.
  have htwo : (2 : Func E) = 0 := by
    have h : (2 : Func E) = algebraMap L (Func E) (2 : L) := natCast_eq_algebraMap E 2
    rw [h, h2, map_zero]
  have hneg (z : Func E) : -z = z := by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, htwo, zero_mul]
  have hqe_eq : (u₂ / N₂) * eK E = h + negAlgEquiv E h := by
    rw [hT_eq, show (2 : Func E) * (u₁ / N₂) = 0 from by rw [htwo, zero_mul], zero_sub,
      hneg]
  have hN_eq : (u₁ / N₂) ^ 2 + (u₁ / N₂) * ((u₂ / N₂) * eK E) + (u₂ / N₂) ^ 2 * cK E =
      h * negAlgEquiv E h := by
    rw [hNm_eq, sub_eq_add_neg, sub_eq_add_neg, hneg, hneg]
    first | refl_ring1 | ring
  -- Step 4: both lie in `L[x]` (integral over `L[x]` and in `L(x)`).
  have hqe_mem : (u₂ / N₂) * eK E ∈ Set.range (xPsi E) :=
    mem_range_xPsi_mul E hq (eK_mem_range_xPsi E)
  have hN_mem : (u₁ / N₂) ^ 2 + (u₁ / N₂) * ((u₂ / N₂) * eK E) + (u₂ / N₂) ^ 2 * cK E ∈
      Set.range (xPsi E) :=
    mem_range_xPsi_add E
      (mem_range_xPsi_add E (mem_range_xPsi_pow E hp 2)
        (mem_range_xPsi_mul E hp (mem_range_xPsi_mul E hq (eK_mem_range_xPsi E))))
      (mem_range_xPsi_mul E (mem_range_xPsi_pow E hq 2) (cK_mem_range_xPsi E))
  have hqe_Ax : (u₂ / N₂) * eK E ∈ Ax E :=
    mem_Ax_of_isIntegral_of_mem_range_xPsi E hqe_mem (hqe_eq.symm ▸ hTAx)
  have hN_Ax : (u₁ / N₂) ^ 2 + (u₁ / N₂) * ((u₂ / N₂) * eK E) + (u₂ / N₂) ^ 2 * cK E ∈
      Ax E :=
    mem_Ax_of_isIntegral_of_mem_range_xPsi E hN_mem (hN_eq.symm ▸ hNAx)
  -- Step 5: the characteristic-two crux.
  obtain ⟨hp_Ax, hq_Ax⟩ :=
    CharTwoNormCrux L E h2 (u₁ / N₂) (u₂ / N₂) hp hq hqe_Ax hN_Ax
  rw [hh_eq]
  have hyR : genY E ∈ affRing E := by
    rw [affRing_eq_adjoin L E]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  have hmem : u₁ / N₂ + (u₂ / N₂) * genY E ∈ affRing E :=
    add_mem (Ax_le_affRing E hp_Ax) (mul_mem (Ax_le_affRing E hq_Ax) hyR)
  simpa using hmem

end Work.MotC2
