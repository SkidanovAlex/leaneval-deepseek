import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.isCompact_matBallToPO
import Submission.Work.Mostow.Margulis.exists_pair_dist_le_bdd
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.margulisPigeonholeAux
import Submission.Work.Mostow.parabolicPow
import Submission.Work.Mostow.finite_translates_inter_compact

/-! Guidance from the project lead (the requester):

# margulisCusp — the Margulis/Zassenhaus lemma in the form the cusp theory needs (lead's design)

Statement: for every R there is ε > 0 such that in ANY discrete Γ: if a parabolic q ∈ Γ fixing ξ moves u by < ε, then
EVERY δ ∈ Γ moving u by ≤ R fixes ξ. (Torsion allowed; δ may be elliptic, parabolic or loxodromic.)
Consequences (for the geomFinite owner): two parabolics of Γ moving the same point by < ε have the same fixed point;
the region U_ξ = {u : some parabolic of Γ fixing ξ moves u < ε} satisfies γ U_ξ ∩ U_ξ = ∅ for γ ∉ Γ_ξ.

## Route (dispatch the pieces in parallel)
Norm: Euclidean operator norm ‖·‖ on (Fin n ⊕ Fin 1)-matrices. For g ∈ PO use its O⁺-lift L(g) (the representative
with positive time–time entry: `tsign (rep g) • mat (rep g)`); L is a group homomorphism PO → matrices (sheet lemma).
Z1 `comm_shrink` (pure matrices): ‖[A,C] − 1‖ ≤ 2‖A − 1‖·‖C − 1‖·‖A⁻¹‖·‖C⁻¹‖ and
    ‖[A,C] − 1‖ ≤ 2‖A − 1‖·‖C‖·‖A⁻¹‖·‖C⁻¹‖, from AC − CA = (A−1)(C−1) − (C−1)(A−1) = (A−1)C − C(A−1).
Z2 `conj_to_origin`: for u, the boost h = B_u (h•0 = u) gives hdist u (g•u) = hdist 0 ((h⁻¹gh)•0); for g with
    hdist 0 (g•0) ≤ R: ‖L g‖, ‖L g⁻¹‖ ≤ C(R) (L g = B_v · diag(Q,1), ‖v‖ ≤ sinh R, ‖B_v‖ ≤ 2 cosh R-type bound).
Z3 `rot_pigeonhole` (see rotPigeonhole.lean in the workspace): ∀ η > 0 ∃ N ∃ ε₀ > 0: if hdist 0 (g•0) < ε₀ then
    ∃ 1 ≤ m ≤ N, ‖L(g^m) − 1‖ < η. (Cover O(n) by N balls of radius η/4; among g^0..g^N two rotation parts are close;
    translation parts are ≤ sinh(N ε₀) small.)
Z4 `discrete_near_one_finite`: Γ discrete ⇒ {γ ∈ Γ : ‖L(h⁻¹γh) − 1‖ ≤ 1/2} finite for any h (discrete ∩ compact;
    compactness: L⁻¹(closed ball) is compact in PO — use POActionProp continuity/ Ksub_compact / isCompact_matBallToPO).
    Hence: a sequence c_j ∈ Γ with ‖L(h⁻¹c_jh) − 1‖ → 0 is eventually 1.
Z5 `parabolic_pow`: q parabolic ⇒ q^m parabolic for m ≥ 1, and its unique boundary fixed point is the same ξ.
    (No fixed point: a fixed point of q^m gives a finite q-orbit ⇒ a fixed point of q (circumcentre / exists_min_circum).
    Infimal displacement of q^m ≤ m · that of q = 0. Unique fixed point: H9's geomFiniteParabolicClass.)
Z6 `comm_fix_back`: a parabolic with unique boundary fixed point ξ; if bd [a,c] ξ = ξ then bd c ξ = ξ.
    Proof: a c a⁻¹ c⁻¹ ξ = ξ ⇒ c a⁻¹ c⁻¹ ξ = a⁻¹ξ = ξ ⇒ a⁻¹ fixes c⁻¹ξ ⇒ c⁻¹ξ = ξ (a⁻¹ parabolic, same unique fixed pt).
Z7 assembly: conjugate u to 0 (Z2; the conjugate group is discrete). Choose η ≤ 1/(16·C(R)⁴) and ε ≤ ε₀(η)/N(η)
    (Z3), so a := q^m (1 ≤ m ≤ N) has ‖L a − 1‖ < η (and ‖La⁻¹‖ ≤ 2). c₀ := δ, c_{j+1} := [a, c_j]. By Z1:
    ‖c₁ − 1‖ ≤ 1/2 and then ‖c_{j+1} − 1‖ ≤ ½ ‖c_j − 1‖ (use ‖c_j⁻¹‖ ≤ 2 once ‖c_j − 1‖ ≤ 1/2). Z4 ⇒ c_N = 1 for
    some N. Backward induction with Z6 (a = q^m, parabolic with fixed point ξ by Z5): c_N = 1 fixes ξ ⇒ … ⇒ c₀ = δ fixes ξ.
## Not needed
No nilpotency theory, no classification of elementary groups, no Jordan theorem, no Bieberbach.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

noncomputable section

variable {n : ℕ}

/-! ## Glue lemmas: conjugation and powers -/

/-- `bd g⁻¹ ∘ bd g = id` on the boundary sphere. -/
lemma bd_inv_bd (hA : POActionProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd g⁻¹ (bd g ξ) = ξ := by
  have hA' := POBasic.ofProp hA
  have h1 : bd (g⁻¹ * g) ξ = bd g⁻¹ (bd g ξ) := hA'.bd_mul g⁻¹ g ξ hξ
  rw [inv_mul_cancel, hA'.bd_one ξ hξ] at h1
  exact h1.symm

/-- The boundary fixed points of a conjugate are the images of the boundary fixed points. -/
lemma bd_conj_fix_iff (hA : POActionProp n) {h g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n) :
    bd (h⁻¹ * g * h) (bd h⁻¹ ξ) = bd h⁻¹ ξ ↔ bd g ξ = ξ := by
  have hA' := POBasic.ofProp hA
  have hmem : bd h⁻¹ ξ ∈ Sph n := hA'.bd_mem h⁻¹ ξ hξ
  have hstep : bd h (bd h⁻¹ ξ) = ξ := by
    have h := hA'.bd_mul h h⁻¹ ξ hξ
    rw [mul_inv_cancel, hA'.bd_one ξ hξ] at h
    exact h.symm
  have hkey : bd h (bd (h⁻¹ * g * h) (bd h⁻¹ ξ)) = bd g ξ := by
    rw [← hA'.bd_mul h (h⁻¹ * g * h) (bd h⁻¹ ξ) hmem]
    have h1 : h * (h⁻¹ * g * h) = g * h := by group
    rw [h1, hA'.bd_mul g h (bd h⁻¹ ξ) hmem, hstep]
  constructor
  · intro hfix
    have h2 : bd g ξ = bd h (bd h⁻¹ ξ) := by rw [← hkey, hfix]
    rw [hstep] at h2
    exact h2
  · intro hfix
    have h2 : bd h (bd (h⁻¹ * g * h) (bd h⁻¹ ξ)) = bd h (bd h⁻¹ ξ) := by
      rw [hkey, hfix, hstep]
    have h3 := congrArg (bd h⁻¹) h2
    rw [bd_inv_bd hA (hA'.bd_mem (h⁻¹ * g * h) (bd h⁻¹ ξ) hmem), bd_inv_bd hA hmem] at h3
    exact h3

/-- A boundary fixed point is fixed by every power. -/
lemma bd_pow_fix (hA : POActionProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n)
    (h : bd g ξ = ξ) (m : ℕ) : bd (g ^ m) ξ = ξ := by
  have hA' := POBasic.ofProp hA
  induction m with
  | zero => rw [pow_zero]; exact hA'.bd_one ξ hξ
  | succ k ih => rw [pow_succ, hA'.bd_mul (g ^ k) g ξ hξ, h, ih]

/-- The inverse of a parabolic isometry is parabolic. -/
lemma isParabolic_inv (hA : POActionProp n) (hI : HypIsometryProp n) {g : PO n 1}
    (hg : IsParabolic g) : IsParabolic g⁻¹ := by
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  constructor
  · intro u hu
    exact hg.1 u (by
      have h1 : g • u = g • (g⁻¹ • u) := by rw [hu]
      rw [h1, ← hA'.mul_smul g g⁻¹ u, mul_inv_cancel, hA'.one_smul])
  · intro ε hε
    obtain ⟨u, hu⟩ := hg.2 ε hε
    refine ⟨g • u, ?_⟩
    have h1 : g⁻¹ • (g • u) = u := by
      rw [← hA'.mul_smul g⁻¹ g u, inv_mul_cancel, hA'.one_smul]
    rw [h1, hI'.symm]
    exact hu

/-- Conjugation of a power by a fixed element. -/
lemma conj_pow {G : Type*} [Group G] (h g : G) (m : ℕ) :
    h * g ^ m * h⁻¹ = (h * g * h⁻¹) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : h * g ^ (k + 1) * h⁻¹ = (h * g ^ k * h⁻¹) * (h * g * h⁻¹) := by group
      rw [h1, ih, ← pow_succ]

/-- The sheet-preserving lift detects the identity. -/
lemma ToO_eq_one_iff (hA : POActionProp n) (g : PO n 1) : ToO g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have hmat : LambdaMat g = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
      have h1 := congrArg mat h
      rwa [mat_ToO, mat_one_coe] at h1
    have hfix : ∀ u : E n, g • u = u := by
      intro u
      apply hlift_injective
      rw [hlift_LambdaMat hA g u, hmat, Matrix.one_mulVec]
    exact (POBasic.ofProp hA).faithful g hfix
  · rintro rfl
    exact ToO_one hA

/-- The displacement of `u` under `g` is the displacement of the origin under the conjugate. -/
lemma hdist_conj_base (hA : POActionProp n) (hI : HypIsometryProp n) {h : PO n 1} {u : E n}
    (hh : h • (0 : E n) = u) (g : PO n 1) :
    hdist (0 : E n) ((h⁻¹ * g * h) • (0 : E n)) = hdist u (g • u) := by
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  have h1 : (h⁻¹ * g * h) • (0 : E n) = h⁻¹ • (g • u) := by
    rw [hA'.mul_smul (h⁻¹ * g) h (0 : E n), hA'.mul_smul h⁻¹ g (h • (0 : E n)), hh]
  rw [h1]
  have h2 : hdist (0 : E n) (h⁻¹ • (g • u))
      = hdist (h • (0 : E n)) (h • (h⁻¹ • (g • u))) :=
    (hI'.isom_smul h (0 : E n) (h⁻¹ • (g • u))).symm
  rw [h2, hh]
  have h3 : h • (h⁻¹ • (g • u)) = g • u := by
    rw [← hA'.mul_smul h h⁻¹ (g • u), mul_inv_cancel, hA'.one_smul]
  rw [h3]

/-- The near-stabiliser of an arbitrary base point in a discrete group is finite. -/
lemma finite_nearStab_any_base (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) (u : E n) (R : ℝ) :
    {γ : Γ | hdist u ((γ : PO n 1) • u) ≤ R}.Finite := by
  have hI' := HypIsoData.ofProp hI
  have hK1 : IsCompact ({u} : Set (E n)) := isCompact_singleton
  have hK2 : IsCompact {v : E n | hdist u v ≤ R} := hI'.ball_compact u R
  have h := finite_translates_inter_compact n hA hI hdisc hK1 hK2
  refine h.subset ?_
  rintro γ hγ
  exact ⟨(γ : PO n 1) • u, ⟨u, by simp, rfl⟩, hγ⟩

/-- `bd [p, c] ξ = ξ` with `p` parabolic fixing `ξ` forces `bd c ξ = ξ`. -/
lemma comm_fix_back (hA : POActionProp n) (hI : HypIsometryProp n) {p c : PO n 1} {ξ : E n}
    (hξ : ξ ∈ Sph n) (hp : IsParabolic p) (hpξ : bd p ξ = ξ)
    (hcomm : bd (p * c * p⁻¹ * c⁻¹) ξ = ξ) : bd c ξ = ξ := by
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  have hX : bd c⁻¹ ξ ∈ Sph n := hA'.bd_mem c⁻¹ ξ hξ
  have hY : bd p⁻¹ (bd c⁻¹ ξ) ∈ Sph n := hA'.bd_mem p⁻¹ (bd c⁻¹ ξ) hX
  have hZ : bd c (bd p⁻¹ (bd c⁻¹ ξ)) ∈ Sph n := hA'.bd_mem c (bd p⁻¹ (bd c⁻¹ ξ)) hY
  have hexp : bd (p * c * p⁻¹ * c⁻¹) ξ = bd p (bd c (bd p⁻¹ (bd c⁻¹ ξ))) := by
    rw [hA'.bd_mul (p * c * p⁻¹) c⁻¹ ξ hξ, hA'.bd_mul (p * c) p⁻¹ (bd c⁻¹ ξ) hX,
      hA'.bd_mul p c (bd p⁻¹ (bd c⁻¹ ξ)) hY]
  have hkey : bd p (bd c (bd p⁻¹ (bd c⁻¹ ξ))) = ξ := by
    rw [← hexp]; exact hcomm
  have hpξ' : bd p⁻¹ ξ = ξ := by
    have h := congrArg (bd p⁻¹) hpξ
    rw [bd_inv_bd hA hξ] at h
    exact h.symm
  have h1 : bd c (bd p⁻¹ (bd c⁻¹ ξ)) = bd p⁻¹ ξ := by
    have h := congrArg (bd p⁻¹) hkey
    rw [bd_inv_bd hA hZ] at h
    exact h
  have h3 : bd p⁻¹ (bd c⁻¹ ξ) = bd c⁻¹ ξ := by
    have h := congrArg (bd c⁻¹) (h1.trans hpξ')
    rw [bd_inv_bd hA hY] at h
    exact h
  have hXeq : bd c⁻¹ ξ = ξ :=
    paraUniqueFixed hA' hI' (isParabolic_inv hA hI hp) hξ hpξ' hX h3
  have h4 : bd c (bd c⁻¹ ξ) = ξ := by
    have h := hA'.bd_mul c c⁻¹ ξ hξ
    rw [mul_inv_cancel, hA'.bd_one ξ hξ] at h
    exact h.symm
  rw [hXeq] at h4
  exact h4

/-! ## The main theorem -/

theorem margulisCusp (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
      ∀ (u ξ : E n) (q δ : Γ), IsParabolic (q : PO n 1) → ξ ∈ Sph n → bd (q : PO n 1) ξ = ξ →
        hdist u ((q : PO n 1) • u) < ε → hdist u ((δ : PO n 1) • u) ≤ R →
        bd (δ : PO n 1) ξ = ξ := by
  intro R
  have hA' := POBasic.ofProp hA
  have hI' := HypIsoData.ofProp hI
  -- the entrywise defect bound for the conjugated `δ`
  set C : ℝ := Real.cosh (max R 0) + 1 with hCdef
  have hCpos : 0 < C := by
    have h := Real.one_le_cosh (max R 0)
    rw [hCdef]; linarith
  have hmsz : 0 < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
  -- the size of the near-identity element
  set η : ℝ := min (1 / 2) (1 / (8 * (msz n) ^ 3 * (1 + C))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    refine lt_min (by norm_num) ?_
    positivity
  have hηsmall : 2 * (msz n) ^ 3 * η * (1 + η) * (1 + C) ≤ 1 / 2 := by
    have h2 : η ≤ 1 / (8 * (msz n) ^ 3 * (1 + C)) := by rw [hηdef]; exact min_le_right _ _
    have h1η : 1 + η ≤ 3 / 2 := by
      have h := min_le_left (1 / 2 : ℝ) (1 / (8 * (msz n) ^ 3 * (1 + C)))
      have h2' : η ≤ 1 / 2 := by rw [hηdef]; exact h
      linarith
    have h3 : 2 * (msz n) ^ 3 * η ≤ 2 * (msz n) ^ 3 * (1 / (8 * (msz n) ^ 3 * (1 + C))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : 2 * (msz n) ^ 3 * (1 / (8 * (msz n) ^ 3 * (1 + C))) = 1 / (4 * (1 + C)) := by
      field_simp
      ring
    rw [h4] at h3
    have h5 : 2 * (msz n) ^ 3 * η * (1 + η) ≤ (1 / (4 * (1 + C))) * (3 / 2) :=
      calc 2 * (msz n) ^ 3 * η * (1 + η) ≤ (1 / (4 * (1 + C))) * (1 + η) :=
            mul_le_mul_of_nonneg_right h3 (by linarith)
        _ ≤ (1 / (4 * (1 + C))) * (3 / 2) :=
            mul_le_mul_of_nonneg_left h1η (by positivity)
    calc 2 * (msz n) ^ 3 * η * (1 + η) * (1 + C)
        ≤ (1 / (4 * (1 + C))) * (3 / 2) * (1 + C) :=
          mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = 3 / 8 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  -- the bounded-power pigeonhole
  have hpig := CuspPig.margulisPigeonhole n hA hI
  have hparpow : ∀ (g : PO n 1), IsParabolic g → ∀ m : ℕ, 0 < m → IsParabolic (g ^ m) :=
    fun g hg m hm => parabolicPow n hA hI hg hm
  obtain ⟨N, hNpos, ε₀, hε₀pos, hpig'⟩ := hpig η hηpos
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro Γ hdisc u ξ q δ hq hξ hqξ hqu hδR
  by_cases hR0 : 0 ≤ R
  · -- conjugate so that the base point becomes the origin
    obtain ⟨h, hh⟩ := (BoostTransitive n hA).1 u
    have hconj : ∀ g : PO n 1,
        hdist (0 : E n) ((h⁻¹ * g * h) • (0 : E n)) = hdist u (g • u) :=
      fun g => hdist_conj_base hA hI hh g
    set q₀ : PO n 1 := h⁻¹ * (q : PO n 1) * h with hq₀def
    set δ₀ : PO n 1 := h⁻¹ * (δ : PO n 1) * h with hδ₀def
    have hq₀disc : hdist (0 : E n) (q₀ • (0 : E n)) < ε₀ := by
      rw [hq₀def]; exact (hconj _).trans_lt hqu
    have hδ₀R : hdist (0 : E n) (δ₀ • (0 : E n)) ≤ R := by
      rw [hδ₀def]; exact (hconj _).trans_le hδR
    have hδ₀C : Near1 (ToO δ₀) C := by
      have h := Near1_ToO_of_hdist (le_max_right R 0) (le_trans hδ₀R (le_max_left R 0))
      rwa [hCdef]
    -- a bounded power of the parabolic is entrywise near the identity
    obtain ⟨m, hm0, hmN, hmη⟩ := hpig' q₀ hq₀disc
    -- the boundary fixed point of the conjugate
    set ξ₀ : E n := bd h⁻¹ ξ with hξ₀def
    have hξ₀mem : ξ₀ ∈ Sph n := hA'.bd_mem h⁻¹ ξ hξ
    have hstep : bd h (bd h⁻¹ ξ) = ξ := by
      have h := hA'.bd_mul h h⁻¹ ξ hξ
      rw [mul_inv_cancel, hA'.bd_one ξ hξ] at h
      exact h.symm
    have hq₀fix : bd q₀ ξ₀ = ξ₀ := by
      have h1 : bd q₀ ξ₀ = bd (h⁻¹ * (q : PO n 1)) ξ := by
        rw [hq₀def, hξ₀def]
        rw [hA'.bd_mul (h⁻¹ * (q : PO n 1)) h (bd h⁻¹ ξ) (hA'.bd_mem h⁻¹ ξ hξ)]
        rw [hstep]
      have h2 : bd (h⁻¹ * (q : PO n 1)) ξ = bd h⁻¹ ξ := by
        rw [hA'.bd_mul h⁻¹ (q : PO n 1) ξ hξ, hqξ]
      rw [h1, h2, hξ₀def]
    have hq₀par : IsParabolic q₀ := by
      rw [hq₀def]
      simpa [inv_inv] using isParabolic_conj hA hI h⁻¹ (q : PO n 1) hq
    have hq₀mpar : IsParabolic (q₀ ^ m) := hparpow q₀ hq₀par m hm0
    have hq₀mfix : bd (q₀ ^ m) ξ₀ = ξ₀ := bd_pow_fix hA hξ₀mem hq₀fix m
    -- the corresponding sequence of elements of `Γ`
    have hconjpow : h * (q₀ ^ m) * h⁻¹ = (q : PO n 1) ^ m := by
      rw [hq₀def]
      have h1 : h * (h⁻¹ * (q : PO n 1) * h) * h⁻¹ = (q : PO n 1) := by group
      rw [conj_pow, h1]
    have hmem : ∀ j : ℕ, h * ci (q₀ ^ m) δ₀ j * h⁻¹ ∈ Γ := by
      intro j
      induction j with
      | zero =>
          rw [ci_zero, hδ₀def]
          have h1 : h * (h⁻¹ * (δ : PO n 1) * h) * h⁻¹ = (δ : PO n 1) := by group
          rw [h1]
          exact δ.2
      | succ k ih =>
          rw [ci_succ]
          have heq : h * ((q₀ ^ m) * ci (q₀ ^ m) δ₀ k * (q₀ ^ m)⁻¹ * (ci (q₀ ^ m) δ₀ k)⁻¹) * h⁻¹
              = (h * (q₀ ^ m) * h⁻¹) * (h * ci (q₀ ^ m) δ₀ k * h⁻¹)
                * (h * (q₀ ^ m) * h⁻¹)⁻¹ * (h * ci (q₀ ^ m) δ₀ k * h⁻¹)⁻¹ := by group
          rw [heq, hconjpow]
          exact mul_mem (mul_mem (mul_mem (pow_mem q.2 m) ih) (inv_mem (pow_mem q.2 m))) (inv_mem ih)
    let bj : ℕ → Γ := fun j => ⟨h * ci (q₀ ^ m) δ₀ j * h⁻¹, hmem j⟩
    have hbj_eq : ∀ j : ℕ, ci (q₀ ^ m) δ₀ j = h⁻¹ * ((bj j : Γ) : PO n 1) * h := by
      intro j
      simp only [bj, Subtype.coe_mk]
      group
    -- the defects of the iterated commutators shrink geometrically
    have hdef : ∀ j : ℕ, Near1 (ToO (ci (q₀ ^ m) δ₀ j)) ((1 / 2 : ℝ) ^ j * C) :=
      toO_ci_shrink' n hA hmη hηpos.le hδ₀C (le_of_lt hCpos) (le_refl C) (le_of_lt hCpos) hηsmall
    -- the finite set of group elements displacing `u` boundedly
    have hF : {γ : Γ | hdist u ((γ : PO n 1) • u) ≤ Real.arcosh (1 + C)}.Finite :=
      finite_nearStab_any_base hA hI hdisc u _
    have hmemF : ∀ j : ℕ,
        bj j ∈ {γ : Γ | hdist u ((γ : PO n 1) • u) ≤ Real.arcosh (1 + C)} := by
      intro j
      have h1 : hdist (0 : E n) (ci (q₀ ^ m) δ₀ j • (0 : E n))
          ≤ Real.arcosh (1 + (1 / 2 : ℝ) ^ j * C) :=
        hdist_le_of_Near1_ToO hA (by positivity) (hdef j)
      have h2 : hdist (0 : E n) (ci (q₀ ^ m) δ₀ j • (0 : E n))
          = hdist u (((bj j : Γ) : PO n 1) • u) := by
        rw [hbj_eq j]
        exact hconj _
      rw [h2] at h1
      have h4 : (1 + (1 / 2 : ℝ) ^ j * C) ≤ 1 + C := by
        have h5 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith [hCpos.le]
      have h6 : (0 : ℝ) < 1 + (1 / 2 : ℝ) ^ j * C := by
        have h7 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j * C :=
          mul_nonneg (pow_nonneg (by norm_num) j) (le_of_lt hCpos)
        linarith
      have h8 : (0 : ℝ) < 1 + C := by linarith
      exact le_trans h1 ((Real.arcosh_le_arcosh h6 h8).mpr h4)
    -- some element of the finite set is taken infinitely often
    have hrange : (Set.range bj).Finite := hF.subset (by rintro γ ⟨j, rfl⟩; exact hmemF j)
    obtain ⟨γ, hγrange, hγinf⟩ : ∃ γ ∈ Set.range bj, ({j : ℕ | bj j = γ}).Infinite := by
      by_contra h
      have h' : ∀ γ ∈ Set.range bj, ({j : ℕ | bj j = γ}).Finite := by
        intro γ hγ
        by_contra h2
        exact h ⟨γ, hγ, h2⟩
      have hunion : (⋃ γ ∈ Set.range bj, {j : ℕ | bj j = γ}) = Set.univ := by
        ext j
        constructor
        · intro _; trivial
        · intro _
          exact Set.mem_biUnion (Set.mem_range_self j) rfl
      have hfin : (Set.univ : Set ℕ).Finite := by
        rw [← hunion]
        exact Set.Finite.biUnion hrange h'
      exact Set.infinite_univ hfin
    -- the corresponding element of `Γ` has arbitrarily small defect
    have hγprop : ∀ q' : ℝ, 0 < q' → Near1 (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) q' := by
      intro q' hq'
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / q') (show (1 : ℝ) < 2 by norm_num)
      rw [div_lt_iff₀ hq'] at hk
      have hk2 : C < q' * 2 ^ k := by rw [mul_comm]; exact hk
      have hk' : (1 / 2 : ℝ) ^ k * C < q' := by
        have h6 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
        calc (1 / 2 : ℝ) ^ k * C < (1 / 2 : ℝ) ^ k * (q' * 2 ^ k) :=
              mul_lt_mul_of_pos_left hk2 (pow_pos (by norm_num) k)
          _ = q' := by
              calc (1 / 2 : ℝ) ^ k * (q' * 2 ^ k) = q' * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by ring
                _ = q' := by rw [h6, mul_one]
      obtain ⟨j, hjmem, hjk⟩ := hγinf.exists_gt k
      have hj : bj j = γ := hjmem
      have hbound : Near1 (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) ((1 / 2 : ℝ) ^ j * C) := by
        have h1 : mat (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) = mat (ToO (ci (q₀ ^ m) δ₀ j)) := by
          rw [hbj_eq j, hj]
        exact (Near1.of_mat_eq h1).mpr (hdef j)
      have h3 : (1 / 2 : ℝ) ^ j * C ≤ (1 / 2 : ℝ) ^ k * C :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt hjk)) (le_of_lt hCpos)
      exact fun i j' => le_trans (hbound i j') (le_trans h3 (le_of_lt hk'))
    -- hence `γ = 1`
    have hγ1 : γ = 1 := by
      have h0 : Near1 (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) 0 := by
        intro i j
        by_contra hlt
        have hlt' : (0 : ℝ) < |mat (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) i j - dE n i j| :=
          lt_of_not_ge hlt
        have hpos : 0 < |mat (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) i j - dE n i j| / 2 := by
          linarith
        have h2 := hγprop _ hpos i j
        linarith
      have hToO : ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h) = 1 := by
        apply O1.mat_injective
        rw [mat_one_coe]
        ext i j
        show mat (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) i j = dE n i j
        have h2 : |mat (ToO (h⁻¹ * ((γ : Γ) : PO n 1) * h)) i j - dE n i j| = 0 :=
          le_antisymm (h0 i j) (abs_nonneg _)
        exact sub_eq_zero.mp (abs_eq_zero.mp h2)
      have h7 : h⁻¹ * ((γ : Γ) : PO n 1) * h = 1 := (ToO_eq_one_iff hA _).mp hToO
      have h8 : (γ : PO n 1) = 1 := by
        have h9 := congrArg (fun x => h * x * h⁻¹) h7
        simpa [mul_assoc] using h9
      exact Subtype.ext h8
    -- so some term of the sequence is `1`
    obtain ⟨j₀, hj₀⟩ := hγrange
    have hbj1 : ∃ N' : ℕ, bj N' = 1 := ⟨j₀, by rw [hj₀, hγ1]⟩
    obtain ⟨N', hbjN'⟩ := hbj1
    -- descending induction on the iterated commutators
    have hPN : bd (ci (q₀ ^ m) δ₀ N') ξ₀ = ξ₀ := by
      have h1 : ci (q₀ ^ m) δ₀ N' = 1 := by
        rw [hbj_eq N', hbjN']
        simp
      rw [h1]
      exact hA'.bd_one ξ₀ hξ₀mem
    have hstep' : ∀ j : ℕ, bd (ci (q₀ ^ m) δ₀ (j + 1)) ξ₀ = ξ₀ →
        bd (ci (q₀ ^ m) δ₀ j) ξ₀ = ξ₀ := by
      intro j hj
      have hcomm : bd ((q₀ ^ m) * ci (q₀ ^ m) δ₀ j * (q₀ ^ m)⁻¹ * (ci (q₀ ^ m) δ₀ j)⁻¹) ξ₀ = ξ₀ := by
        rw [← ci_succ]; exact hj
      exact comm_fix_back hA hI hξ₀mem hq₀mpar hq₀mfix hcomm
    have hall : ∀ j : ℕ, j ≤ N' → bd (ci (q₀ ^ m) δ₀ j) ξ₀ = ξ₀ := by
      intro j hj
      exact Nat.decreasingInduction (motive := fun j _ => bd (ci (q₀ ^ m) δ₀ j) ξ₀ = ξ₀)
        (fun k _ ih => hstep' k ih) hPN hj
    have hδ₀fix : bd δ₀ ξ₀ = ξ₀ := hall 0 (Nat.zero_le N')
    -- transfer back to `δ` and `ξ`
    exact (bd_conj_fix_iff hA hξ).mp hδ₀fix
  · -- `R < 0`: nothing displaces `u` by at most `R`
    exfalso
    have h := hI'.nonneg u ((δ : PO n 1) • u)
    linarith

end

end Work.Mostow
