import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.NeTwoSquarefreeCubic
import Submission.Work.MotC2.NeTwoNoDoubleRoot
import Submission.Work.MotC2.NeTwoRatFuncSqMul
import Submission.Work.MotC2.NeTwoIsIntegralMap
import Submission.Work.MotC2.NeTwoDecomp
import Submission.Work.MotC2.NeTwoSquarefreeDAux
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

/-- Normality of the affine coordinate ring in characteristic ≠ 2: `affRing E = L[x,y]` is
integrally closed in `L(E)`.

Route (trace/norm over `L(x)`; `x = genX E`, `y = genY E`, `e = a₁x + a₃`, `c = x³ + a₂x² + a₄x + a₆`,
so `y² + e·y = c`).

1. The conjugation `σ : K ≃ₐ[L] K` with `σ x = x`, `σ y = -y - e` exists (the conjugate of `y`
   satisfies the same Weierstrass equation), is an involution, and preserves `R = L[x,y]` and `L[x]`.
   Build it from the `L`-algebra hom `Coord E →ₐ[L] K`, `coordX ↦ x`, `coordY ↦ -y-e`, extended to
   `K = Frac (Coord E)` by `IsFractionRing`/`IsLocalization.liftAlgHom` (injectivity: the image is
   not `L`).
2. Let `h ∈ K` be integral over `R`.  Then `σ h` is integral over `R`, so `T := h + σh` and
   `N := h·σh` are integral over `R`, hence over `L[x]`; both lie in `L(x)` (either because `L(x)`
   is the fixed field of `σ`, or by writing `h = (P + Q·y)/D` with `P Q D ∈ L[x]`, `D ≠ 0`, and
   computing `T = (2P - Qe)/D`, `N = (P² - PQe - Q²c)/D²`).  As `L[x]` is integrally closed in
   `L(x)` (it is a PID/UFD), `T, N ∈ L[x]`.
3. Write `h = p + q·y` with `p, q ∈ L(x)`.  Then `T = 2p - qe` and `N = p² - pqe - q²c`, hence
   `T² - 4N = q²·(e² + 4c) = q²·4g`, where `g := x³ + (b₂/4)x² + (b₄/2)x + b₆/4` (roots: the
   x-coordinates of the 2-torsion points).  Since `(2:L) ≠ 0`, `4g` is non-zero and squarefree:
   a repeated root `α` would produce the singular point `(α, -e(α)/2)` of `E`
   (`W_y = 2y + e = 0` and `W_x = a₁y - c' = 0` there), contradicting
   `WeierstrassCurve.Affine.equation_iff_nonsingular` for `E.IsElliptic`.  Hence
   `q²·(4g) ∈ L[x]` forces `q ∈ L[x]` (`L[x]` is a UFD: write `q = A/B` in lowest terms, then
   `B² ∣ 4g` and `4g` squarefree force `B` to be a unit), and then `p = (T + qe)/2 ∈ L[x]`.
   In particular `h = p + q·y ∈ R`. -/
theorem AffRingNormalNeTwo (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) ≠ 0) :
    IsIntegrallyClosedIn ↥((Work.MotC2.affRing E).toSubring) (Work.MotC2.Func E) := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro h hh
  -- Step 0: `h` is integral over `L[x]`.
  have hhAx : IsIntegral ↥(Ax E) h := isIntegral_Ax_of_isIntegral_affRing E hh
  -- Step 1: the conjugate `σ h` is integral over `L[x]` as well, since `σ` fixes `L[x]`.
  have hσhAx : IsIntegral ↥(Ax E) (negAlgEquiv E h) :=
    NeTwoIsIntegralMap (negAlgEquiv E).toRingEquiv.toRingHom (RingHom.id ↥(Ax E))
      (fun r => by
        simp only [RingHom.id_apply]
        exact negAlgEquiv_mem_Ax E r.2)
      hhAx
  have hTAx : IsIntegral ↥(Ax E) (h + negAlgEquiv E h) := hhAx.add hσhAx
  have hNAx : IsIntegral ↥(Ax E) (h * negAlgEquiv E h) := hhAx.mul hσhAx
  -- Step 2: decompose `h` in the `L[x]`-basis `{1, y}` of `L(E)`.
  obtain ⟨b₁, b₂, s₁, s₂, hb₁, hb₂, hs₁, hs₂, hden, hdecomp, hN₂ne, hident⟩ :=
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
  -- the two components `p = u₁/N₂` and `q = u₂/N₂` lie in `L(x) = range (xPsi E)`
  have hp : u₁ / N₂ ∈ Set.range (xPsi E) :=
    mem_range_xPsi_of_mul E hu₁Ax hN₂Ax hN₂ne (by rw [div_mul_cancel₀ _ hN₂ne])
  have hq : u₂ / N₂ ∈ Set.range (xPsi E) :=
    mem_range_xPsi_of_mul E hu₂Ax hN₂Ax hN₂ne (by rw [div_mul_cancel₀ _ hN₂ne])
  have hh_eq : h = u₁ / N₂ + (u₂ / N₂) * genY E := by
    have h1 : u₁ / N₂ + (u₂ / N₂) * genY E = (u₁ + u₂ * genY E) / N₂ := by
      rw [div_mul_eq_mul_div, ← add_div]
    rw [h1, eq_div_iff hN₂ne]
    exact hident
  -- `σ` fixes `L(x)`, so it acts on `h = p + q y` by `p - q e - q y`
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
  -- `T = h + σh` and `Nm = h * σh` lie in `L(x)`
  have h2mem : (2 : Func E) ∈ Set.range (xPsi E) :=
    Ax_subset_range_xPsi E (Subalgebra.natCast_mem (Ax E) 2)
  have hT_mem : h + negAlgEquiv E h ∈ Set.range (xPsi E) := by
    rw [hT_eq, sub_eq_add_neg]
    exact mem_range_xPsi_add E (mem_range_xPsi_mul E h2mem hp)
      (mem_range_xPsi_neg E (mem_range_xPsi_mul E hq (eK_mem_range_xPsi E)))
  have hNm_mem : h * negAlgEquiv E h ∈ Set.range (xPsi E) := by
    rw [hNm_eq]
    exact mem_range_xPsi_sub E
      (mem_range_xPsi_sub E
        (mem_range_xPsi_pow E hp 2)
        (mem_range_xPsi_mul E (mem_range_xPsi_mul E hp hq) (eK_mem_range_xPsi E)))
      (mem_range_xPsi_mul E (mem_range_xPsi_pow E hq 2) (cK_mem_range_xPsi E))
  -- Step 3: since `L[x]` is integrally closed in `L(x)`, `T, Nm ∈ L[x]`
  have hT_Ax : h + negAlgEquiv E h ∈ Ax E :=
    mem_Ax_of_isIntegral_of_mem_range_xPsi E hT_mem hTAx
  have hN_Ax : h * negAlgEquiv E h ∈ Ax E :=
    mem_Ax_of_isIntegral_of_mem_range_xPsi E hNm_mem hNAx
  -- Step 4: `q ^ 2 * (e ^ 2 + 4c) = T ^ 2 - 4 Nm ∈ L[x]`
  have hqD_eq : (u₂ / N₂) ^ 2 * (eK E ^ 2 + 4 * cK E) =
      (h + negAlgEquiv E h) ^ 2 - 4 * (h * negAlgEquiv E h) := by
    rw [hT_eq, hNm_eq]
    first | refl_ring1 | ring
  have hqD_Ax : (u₂ / N₂) ^ 2 * (eK E ^ 2 + 4 * cK E) ∈ Ax E := by
    rw [hqD_eq]
    exact sub_mem (pow_mem hT_Ax 2)
      (mul_mem (Subalgebra.natCast_mem (Ax E) 4) hN_Ax)
  -- Step 5: `q ∈ L[x]`, using that `e ^ 2 + 4c = xPhi (linCoef ^ 2 + 4 cubCoef)` is squarefree
  obtain ⟨w, hw⟩ := hq
  obtain ⟨X₀, hX₀⟩ : ∃ X : Polynomial L, xPhi E X = (u₂ / N₂) ^ 2 * (eK E ^ 2 + 4 * cK E) := by
    rw [← xPhi_range] at hqD_Ax
    exact hqD_Ax
  have hD₀ : Squarefree (linCoef E ^ 2 + 4 * cubCoef E) :=
    NeTwoSquarefreeDAux L E h2 (NeTwoNoDoubleRoot L E h2)
  have key : w ^ 2 * algebraMap (Polynomial L) (RatFunc L) (linCoef E ^ 2 + 4 * cubCoef E) =
      algebraMap (Polynomial L) (RatFunc L) X₀ := by
    apply xPsi_injective E
    rw [map_mul, map_pow, hw, xPsi_apply_algebraMap, xPhi_D E, xPsi_apply_algebraMap, hX₀]
  have hq_Ax : u₂ / N₂ ∈ Ax E := by
    obtain ⟨a, ha⟩ := NeTwoRatFuncSqMul L (linCoef E ^ 2 + 4 * cubCoef E) hD₀ w ⟨X₀, key.symm⟩
    rw [← hw, ← ha, xPsi_apply_algebraMap, ← xPhi_range]
    exact (AlgHom.mem_range (xPhi E)).mpr ⟨a, rfl⟩
  -- Step 6: `p = (T + q e)/2 ∈ L[x]`, and `h = p + q y ∈ affRing E`
  have hp_Ax : u₁ / N₂ ∈ Ax E := by
    have h2p : (2 : Func E) * (u₁ / N₂) =
        (h + negAlgEquiv E h) + (u₂ / N₂) * eK E := by
      rw [hT_eq]
      first | refl_ring1 | ring
    have hmem : (2 : Func E) * (u₁ / N₂) ∈ Ax E := by
      rw [h2p]
      exact add_mem hT_Ax (mul_mem hq_Ax (eK_mem E))
    have htwo : (2 : Func E) = algebraMap L (Func E) (2 : L) := natCast_eq_algebraMap E 2
    have hsplit : u₁ / N₂ = algebraMap L (Func E) ((2 : L)⁻¹) * ((2 : Func E) * (u₁ / N₂)) := by
      rw [htwo, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2, map_one, one_mul]
    rw [hsplit]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hmem
  rw [hh_eq]
  have hyR : genY E ∈ affRing E := by
    rw [affRing_eq_adjoin L E]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  have hmem : u₁ / N₂ + (u₂ / N₂) * genY E ∈ affRing E :=
    add_mem (Ax_le_affRing E hp_Ax) (mul_mem (Ax_le_affRing E hq_Ax) hyR)
  simpa using hmem

end Work.MotC2
