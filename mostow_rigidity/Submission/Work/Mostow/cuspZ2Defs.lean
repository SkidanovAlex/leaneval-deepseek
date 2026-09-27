import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.horoSpec
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.cuspCocompactAllLevels

/-!
# The flat (horospherical) action of a group fixing a boundary point

Let `ξ ∈ Sph n` be a boundary point of `ℍⁿ` and `D > 0`.  The level-`D` horosphere of `ξ` is
flat: in the normalised flat coordinate `yc ξ u ∈ ξ^⊥` of a point `u` of level `D`, the
hyperbolic distance is

`hdist u v = arcosh (1 + (D ‖yc ξ u - yc ξ v‖)² / 2)`   (`hdist_of_lev_eq`, `hdist_yc_eq`),

so `ξ^⊥` (with the Euclidean structure induced from `E n`) is a model of the horosphere as a
Euclidean space, and an isometry of `ℍⁿ` that fixes `ξ` and preserves the horosphere levels acts
on it by a Euclidean isometry:

* `xiPerp ξ = (ℝξ)ᗮ` is the flat space;
* `flatFun hξ D g : xiPerp ξ → xiPerp ξ` is the flat action of `g`, `y ↦ yc ξ (g • hptOf ξ y D)`;
* `flatFun_one`, `flatFun_mul` : `flatFun` is an action;
* `flatFun_dist` : it preserves the Euclidean distance;
* `flatIsom`, `cuspFlatHom` : the corresponding Euclidean isometry and the group homomorphism
  `G →* (xiPerp ξ ≃ᵢ xiPerp ξ)` of a subgroup `G` fixing `ξ` and preserving the levels.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The flat space of the boundary point `ξ`: the orthogonal complement of the line `ℝξ`. -/
def xiPerp (ξ : E n) : Submodule ℝ (E n) := (Submodule.span ℝ ({ξ} : Set (E n)))ᗮ

lemma mem_xiPerp_iff {ξ y : E n} : y ∈ xiPerp ξ ↔ inner ℝ ξ y = 0 := by
  rw [xiPerp, Submodule.mem_orthogonal]
  constructor
  · intro h; exact h ξ (Submodule.mem_span_singleton_self ξ)
  · rintro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [real_inner_smul_left, h, mul_zero]

lemma xiPerp_inner {ξ : E n} (y : xiPerp ξ) : inner ℝ ξ (y : E n) = 0 :=
  mem_xiPerp_iff.mp y.2

lemma xiPerp_inner' {ξ : E n} (y : xiPerp ξ) : inner ℝ (y : E n) ξ = 0 := by
  rw [real_inner_comm]; exact xiPerp_inner y

/-- The flat action of `g` on the level-`D` horosphere of `ξ`, in the normalised flat
coordinate `yc ξ`.  This is well defined for any `g : PO n 1`; the lemmas below need `g` to
preserve the horosphere levels (`∀ u, lev ξ (g • u) = lev ξ u`). -/
def flatFun {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (g : PO n 1) (y : xiPerp ξ) : xiPerp ξ :=
  ⟨yc ξ (g • hptOf ξ (y : E n) D),
    mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact inner_yc hξ _)⟩

@[simp] lemma flatFun_coe {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (g : PO n 1) (y : xiPerp ξ) :
    ((flatFun hξ D g y : xiPerp ξ) : E n) = yc ξ (g • hptOf ξ (y : E n) D) := rfl

/-- The point of level `D` on the horosphere of `ξ` with flat coordinate `yc ξ (g • u)` is
`g • u`, provided `g` preserves the level of `u`. -/
lemma hptOf_yc_eq_of_lev {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1} {u : E n} {D : ℝ}
    (h : lev ξ (g • u) = D) : hptOf ξ (yc ξ (g • u)) D = g • u := by
  rw [← h]; exact hptOf_yc_lev hξ (g • u)

/-- The hyperbolic distance of two points of the same horosphere level `D`, in flat
coordinates: `hdist u v = arcosh (1 + (D ‖yc ξ u - yc ξ v‖)²/2)`. -/
lemma hdist_of_lev_eq {ξ : E n} (hξ : ξ ∈ Sph n) {D : ℝ} (hD : 0 < D) {u v : E n}
    (hu : lev ξ u = D) (hv : lev ξ v = D) :
    hdist u v = Real.arcosh (1 + (D * ‖yc ξ u - yc ξ v‖) ^ 2 / 2) := by
  have hu' : u = hptOf ξ (yc ξ u) D := by
    calc u = hptOf ξ (yc ξ u) (lev ξ u) := (hptOf_yc_lev hξ u).symm
      _ = hptOf ξ (yc ξ u) D := by rw [hu]
  have hv' : v = hptOf ξ (yc ξ v) D := by
    calc v = hptOf ξ (yc ξ v) (lev ξ v) := (hptOf_yc_lev hξ v).symm
      _ = hptOf ξ (yc ξ v) D := by rw [hv]
  have h1 : hdist u v = hdist (hptOf ξ (yc ξ u) D) (hptOf ξ (yc ξ v) D) := by
    conv_lhs => rw [hu', hv']
  rw [h1]
  exact hptOf_hdist ξ hξ D hD (yc ξ u) (yc ξ v) (inner_yc hξ u) (inner_yc hξ v)

/-- The version of `hdist_of_lev_eq` for points of `ξ^⊥`. -/
lemma hdist_yc_eq {ξ : E n} (hξ : ξ ∈ Sph n) {D : ℝ} (hD : 0 < D) (y y' : xiPerp ξ) :
    hdist (hptOf ξ (y : E n) D) (hptOf ξ (y' : E n) D)
      = Real.arcosh (1 + (D * ‖(y : E n) - (y' : E n)‖) ^ 2 / 2) :=
  hptOf_hdist ξ hξ D hD (y : E n) (y' : E n) (xiPerp_inner' y) (xiPerp_inner' y')

/-- The hyperbolic distance in flat coordinates at two possibly different levels:
`hdist u v = arcosh (cosh (log (L/M)) + (L M / 2) ‖yc ξ u - yc ξ v‖²)`. -/
lemma hdist_yc_eq_gen (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) {u v : E n} {L M : ℝ}
    (hu : lev ξ u = L) (hv : lev ξ v = M) :
    hdist u v = Real.arcosh (Real.cosh (Real.log (L / M)) + (L * M / 2) * ‖yc ξ u - yc ξ v‖ ^ 2) := by
  have h := levYcFormula hξ u v
  rw [hu, hv] at h
  rw [← h, Real.arcosh_cosh (hI.nonneg u v)]

/-- `flatFun` of the identity is the identity. -/
lemma flatFun_one {ξ : E n} (hA : POBasic n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (y : xiPerp ξ) : flatFun hξ D 1 y = y := by
  apply Subtype.ext
  rw [flatFun_coe, hA.one_smul]
  exact (hptOfLevelYc ξ hξ (xiPerp_inner' y) hD).2.1

/-- `flatFun` is multiplicative (as an action) whenever the second factor preserves the
horosphere levels. -/
lemma flatFun_mul {ξ : E n} (hA : POBasic n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    {g₁ g₂ : PO n 1} (hlev₂ : ∀ u : E n, lev ξ (g₂ • u) = lev ξ u) (y : xiPerp ξ) :
    flatFun hξ D (g₁ * g₂) y = flatFun hξ D g₁ (flatFun hξ D g₂ y) := by
  apply Subtype.ext
  rw [flatFun_coe, flatFun_coe, flatFun_coe, hA.mul_smul]
  have hlev : lev ξ (g₂ • hptOf ξ (y : E n) D) = D := by
    rw [hlev₂, (hptOfLevelYc ξ hξ (xiPerp_inner' y) hD).1]
  rw [hptOf_yc_eq_of_lev hξ hlev]

/-- `flatFun` of an element preserving the levels is a bijection. -/
lemma flatFun_bijective {ξ : E n} (hA : POBasic n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    {g : PO n 1} (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hlev' : ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u) :
    Function.Bijective (flatFun hξ D g) := by
  have hleft : ∀ y : xiPerp ξ, flatFun hξ D g⁻¹ (flatFun hξ D g y) = y := by
    intro y
    rw [← flatFun_mul hA hξ D hD hlev y, inv_mul_cancel, flatFun_one hA hξ D hD]
  have hright : ∀ y : xiPerp ξ, flatFun hξ D g (flatFun hξ D g⁻¹ y) = y := by
    intro y
    rw [← flatFun_mul hA hξ D hD hlev' y, mul_inv_cancel, flatFun_one hA hξ D hD]
  refine ⟨fun a b hab => ?_, fun y => ⟨flatFun hξ D g⁻¹ y, hright y⟩⟩
  have := congrArg (flatFun hξ D g⁻¹) hab
  rwa [hleft a, hleft b] at this

/-- `flatFun` preserves the Euclidean distance. -/
lemma flatFun_dist (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    {g : PO n 1} (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) (y y' : xiPerp ξ) :
    dist (flatFun hξ D g y) (flatFun hξ D g y') = dist y y' := by
  have hlevy : lev ξ (g • hptOf ξ (y : E n) D) = D := by
    rw [hlev, (hptOfLevelYc ξ hξ (xiPerp_inner' y) hD).1]
  have hlevy' : lev ξ (g • hptOf ξ (y' : E n) D) = D := by
    rw [hlev, (hptOfLevelYc ξ hξ (xiPerp_inner' y') hD).1]
  have hd1 := hdist_of_lev_eq hξ hD hlevy hlevy'
  have hd2 := hdist_of_lev_eq (ξ := ξ) hξ hD
    (hptOfLevelYc ξ hξ (xiPerp_inner' y) hD).1 (hptOfLevelYc ξ hξ (xiPerp_inner' y') hD).1
  have hmain : Real.arcosh (1 + (D * ‖yc ξ (g • hptOf ξ (y : E n) D)
        - yc ξ (g • hptOf ξ (y' : E n) D)‖) ^ 2 / 2)
      = Real.arcosh (1 + (D * ‖yc ξ (hptOf ξ (y : E n) D)
        - yc ξ (hptOf ξ (y' : E n) D)‖) ^ 2 / 2) := by
    rw [← hd1, ← hd2, hI.isom_smul]
  have hle1 : 1 ≤ 1 + (D * ‖yc ξ (g • hptOf ξ (y : E n) D)
        - yc ξ (g • hptOf ξ (y' : E n) D)‖) ^ 2 / 2 := by
    have := sq_nonneg (D * ‖yc ξ (g • hptOf ξ (y : E n) D)
      - yc ξ (g • hptOf ξ (y' : E n) D)‖); linarith
  have hle2 : 1 ≤ 1 + (D * ‖yc ξ (hptOf ξ (y : E n) D)
        - yc ξ (hptOf ξ (y' : E n) D)‖) ^ 2 / 2 := by
    have := sq_nonneg (D * ‖yc ξ (hptOf ξ (y : E n) D)
      - yc ξ (hptOf ξ (y' : E n) D)‖); linarith
  have hcosh := congrArg Real.cosh hmain
  rw [Real.cosh_arcosh hle1, Real.cosh_arcosh hle2] at hcosh
  have hsq : (D * ‖yc ξ (g • hptOf ξ (y : E n) D) - yc ξ (g • hptOf ξ (y' : E n) D)‖) ^ 2
      = (D * ‖yc ξ (hptOf ξ (y : E n) D) - yc ξ (hptOf ξ (y' : E n) D)‖) ^ 2 := by
    linarith
  have hyc : yc ξ (hptOf ξ (y : E n) D) = (y : E n) :=
    (hptOfLevelYc ξ hξ (xiPerp_inner' y) hD).2.1
  have hyc' : yc ξ (hptOf ξ (y' : E n) D) = (y' : E n) :=
    (hptOfLevelYc ξ hξ (xiPerp_inner' y') hD).2.1
  rw [hyc, hyc'] at hsq
  have hX : D * ‖yc ξ (g • hptOf ξ (y : E n) D) - yc ξ (g • hptOf ξ (y' : E n) D)‖
      = D * ‖(y : E n) - (y' : E n)‖ := by
    have hx : 0 ≤ D * ‖yc ξ (g • hptOf ξ (y : E n) D) - yc ξ (g • hptOf ξ (y' : E n) D)‖ :=
      mul_nonneg (le_of_lt hD) (norm_nonneg _)
    have hy : 0 ≤ D * ‖(y : E n) - (y' : E n)‖ := mul_nonneg (le_of_lt hD) (norm_nonneg _)
    calc D * ‖yc ξ (g • hptOf ξ (y : E n) D) - yc ξ (g • hptOf ξ (y' : E n) D)‖
        = Real.sqrt ((D * ‖yc ξ (g • hptOf ξ (y : E n) D)
            - yc ξ (g • hptOf ξ (y' : E n) D)‖) ^ 2) := (Real.sqrt_sq hx).symm
      _ = Real.sqrt ((D * ‖(y : E n) - (y' : E n)‖) ^ 2) := by rw [hsq]
      _ = D * ‖(y : E n) - (y' : E n)‖ := Real.sqrt_sq hy
  have hnorm : ‖yc ξ (g • hptOf ξ (y : E n) D) - yc ξ (g • hptOf ξ (y' : E n) D)‖
      = ‖(y : E n) - (y' : E n)‖ := mul_left_cancel₀ (ne_of_gt hD) hX
  rw [dist_eq_norm, dist_eq_norm, ← Submodule.norm_coe (flatFun hξ D g y - flatFun hξ D g y'),
    ← Submodule.norm_coe (y - y'), Submodule.coe_sub, Submodule.coe_sub, flatFun_coe, flatFun_coe]
  exact hnorm

/-- The Euclidean isometry of the flat space `ξ^⊥` induced by an element `g` fixing the
boundary point `ξ` and preserving the horosphere levels. -/
def flatIsom (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ)
    (hD : 0 < D) {g : PO n 1} (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hlev' : ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u) : xiPerp ξ ≃ᵢ xiPerp ξ :=
  IsometryEquiv.mk (Equiv.ofBijective (flatFun hξ D g) (flatFun_bijective hA hξ D hD hlev hlev'))
    (isometry_iff_dist_eq.mpr (flatFun_dist hI hξ D hD hlev))

@[simp] lemma flatIsom_apply (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) {g : PO n 1} (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hlev' : ∀ u : E n, lev ξ (g⁻¹ • u) = lev ξ u) (y : xiPerp ξ) :
    flatIsom hA hI hξ D hD hlev hlev' y = flatFun hξ D g y := rfl

/-- The flat action of a subgroup `G` of `PO n 1` fixing `ξ` and preserving the horosphere
levels, as a group homomorphism to the Euclidean isometry group of `ξ^⊥`. -/
def cuspFlatHom (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (D : ℝ)
    (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u) : G →* (xiPerp ξ ≃ᵢ xiPerp ξ) where
  toFun g := flatIsom hA hI hξ D hD (fun u => hlev g g.2 u) (fun u => hlev g⁻¹ g⁻¹.2 u)
  map_one' := by
    apply IsometryEquiv.ext
    intro y
    show flatFun hξ D ((1 : G) : PO n 1) y = (1 : xiPerp ξ ≃ᵢ xiPerp ξ) y
    rw [Subgroup.coe_one G, flatFun_one hA hξ D hD]
    rfl
  map_mul' g₁ g₂ := by
    apply IsometryEquiv.ext
    intro y
    show flatFun hξ D (((g₁ * g₂ : G)) : PO n 1) y
      = flatFun hξ D ((g₁ : G) : PO n 1) (flatFun hξ D ((g₂ : G) : PO n 1) y)
    rw [Subgroup.coe_mul, flatFun_mul hA hξ D hD (fun u => hlev g₂ g₂.2 u) y]

@[simp] lemma cuspFlatHom_apply (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u) (g : G) (y : xiPerp ξ) :
    cuspFlatHom hA hI hξ D hD G hlev g y = flatFun hξ D (g : PO n 1) y := rfl

end

end Work.Mostow
