/-
# `Work.ELAssembly.cv_mem_arcSide_of_W0` — the critical value is on the far side of `Q`

**(CV)** of `NOTES_LEAD_mandelbar_hcv.md` §2: if the root wake arc `W₀ = (α₁, α₂)` of the root
portrait is contained in the arc `(I.2, I.1)` of a co-landing pair `Q` — the arc **not** pulled
back by `pb1Top` — then the critical value `c = T_c 0` lies on the side of the pair curve `Q`
that is met by that arc.

The proof has two branches.

* `Q.y ≠ z₁`.  Then the curve of `Q` is disjoint from the curve of the root `α`-pair
  (`pairCurve_disjoint_alpha`), and `Work.ELTop.pairSide_subset_pairSide(Near)` transports the
  known membership `c ∈ pairSide (α-pair)` (`cv_mem_pairSide_alpha`, the L-wake condition
  `d.wake 1`) to the required side of `Q`.
* `Q.y = z₁`.  Then `hzero` (the two-ray portrait at `z₁`) forces both angles of `Q` to be the
  root angles mod `1`, and the orientation hypothesis `hW` — through the arithmetic lemma
  `InArc_W0_orientation` — forces `(I.2, I.1) ≡ (α₁, α₂)`.  The curve and the reference point of
  `arcSide Q I.2 I.1` are then those of the `α`-pair, and the conclusion is again the L-wake
  condition.

The vocabulary bridge `cvside_diag_*` between the canonical `ELPull.DynB c` datum `hNcanOf d`
(whose ray-landing relation agrees with the `Work.EL` one by `Work.PortraitCount.landsN_elDynB`)
and `d.hN` is the same as in `coLand_Q` / `coLand_Z`: `rayPt_eq_of_eqOn_compl` applied to the
equality of the two Böttcher coordinates off the filled Julia set (`hψOf`).
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELTop.pairSide_subset_pairSide
import Submission.Work.FinalFix.Nonreal
import Submission.Work.ELAssembly.eq_alpha_of_landsN_z1
import Submission.Work.ELAssembly.InArc_W0_orientation
import Submission.Work.ELAssembly.pairCurve_disjoint_alpha

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## (H1) the critical value lies in the far side of the `α`-pair -/

/-- The L-wake condition `d.wake 1` says that the critical value `c = T_c 0` lies in the wake
side `X₀`, which is the far side of the root `α`-pair. -/
theorem cv_mem_pairSide_alpha {c : ℂ} (d : Work.EL.RootParabolic c) :
    c ∈ Work.EL.pairSide (alphaPairOf d) := by
  have h := d.wake 1 le_rfl
  have h0 : (1 - 1) % 5 = 0 := by norm_num
  rw [h0] at h
  have h1 : (Tantibar c)^[1] 0 = c := by simp [LeanEval.ComplexAnalysis.Tantibar]
  rw [h1] at h
  rwa [Work.FinalFix.wakeSide_zero_eq_pairSide d (alphaPairOf d) rfl rfl rfl] at h

/-! ## The vocabulary bridge to the canonical `ELPull` data -/

theorem cvside_diag_Phi_eq {c : ℂ} (d : Work.EL.RootParabolic c) {z : ℂ}
    (hz : z ∉ Work.EL.K c) :
    Work.EL.dynPhi c d.φ z = Work.ParamRays.dynPhi c z := by
  rw [Work.EL.dynPhi_of_notMem hz, Work.ParamRays.dynPhi_of_not_mem hz]
  exact hψOf d z hz

/-- The ray points of the canonical `ELPull` data and of `d.hN` agree. -/
theorem cvside_diag_rayPt {c : ℂ} (d : Work.EL.RootParabolic c) (θ t : ℝ) :
    (hNcanOf d).rayPt θ t = d.hN.rayPt θ t :=
  ((rayPt_eq_of_eqOn_compl d.hN (hNcanOf d) (fun z hz => cvside_diag_Phi_eq d hz)).1 θ t).symm

/-- The ray-landing relations of the canonical `ELPull` data and of `d.hN` agree. -/
theorem cvside_diag_landsN {c : ℂ} (d : Work.EL.RootParabolic c) (θ : ℝ) (y : ℂ) :
    Work.ELPull.LandsN (hNcanOf d) θ y ↔ Work.EL.LandsN d.hN θ y :=
  ((rayPt_eq_of_eqOn_compl d.hN (hNcanOf d) (fun z hz => cvside_diag_Phi_eq d hz)).2 θ y).symm

/-- The rays of the canonical `ELPull` data and of `d.hN` agree. -/
theorem cvside_diag_paramRay {c : ℂ} (d : Work.EL.RootParabolic c) (θ : ℝ) :
    Work.Top.NakaneData.paramRay (hNcanOf d) θ = Work.Top.NakaneData.paramRay d.hN θ := by
  ext z
  rw [Work.Top.NakaneData.mem_paramRay_iff, Work.Top.NakaneData.mem_paramRay_iff]
  constructor
  · rintro ⟨hz, t, ht, h⟩
    exact ⟨hz, t, ht, (cvside_diag_Phi_eq d hz).trans h⟩
  · rintro ⟨hz, t, ht, h⟩
    exact ⟨hz, t, ht, (cvside_diag_Phi_eq d hz).symm.trans h⟩

/-- **The vocabulary bridge**: the `ELPull` side of a canonical pair is the `Work.EL` side of the
corresponding raw pair. -/
theorem cvside_diag_arcSide {c : ℂ} (d : Work.EL.RootParabolic c)
    (Q : Work.ELPull.CoPair (hNcanOf d)) (p q : ℝ) :
    Work.ELPull.arcSide (hNcanOf d) Q p q
      = Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) p q := by
  have hray : (hNcanOf d).rayPt (p + Work.ELPull.arcLen p q / 2) 2
      = d.hN.rayPt (p + Work.EL.arcLen p q / 2) 2 := by
    rw [show Work.ELPull.arcLen p q = Work.EL.arcLen p q from rfl]
    exact cvside_diag_rayPt d _ _
  have hcurve : Work.ELPull.pairCurve (hNcanOf d) Q
      = Work.EL.RawPair.curve d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) := by
    simp only [Work.ELPull.pairCurve, Work.EL.RawPair.curve]
    rw [cvside_diag_paramRay d Q.a, cvside_diag_paramRay d Q.b]
  rw [Work.ELPull.arcSide, Work.EL.RawPair.sideThrough, hcurve, hray]

/-! ## Angle arithmetic -/

/-- `InArc` is invariant under an integer translation of the *left* endpoint. -/
theorem cvside_InArc_add_left_int (x a b : ℝ) (m : ℤ) :
    Work.EL.InArc x (a + (m : ℝ)) b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show x - (a + (m : ℝ)) = (x - a) - (m : ℝ) by ring, Int.fract_sub_intCast,
    show b - (a + (m : ℝ)) = (b - a) - (m : ℝ) by ring, Int.fract_sub_intCast]

/-- `a + arcLen a b` is the lift of `b` above `a`. -/
theorem cvside_add_arcLen_eq (a b : ℝ) :
    a + Work.EL.arcLen a b = b + ((-⌊b - a⌋ : ℤ) : ℝ) := by
  unfold Work.EL.arcLen
  have h := Int.fract_add_floor (b - a)
  push_cast
  linarith

/-- `RawPair.sideThrough` only depends on the two angles mod `1`. -/
theorem cvside_sideThrough_congr_arc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (R : Work.EL.RawPair) (p q : ℝ) (m m' : ℤ) :
    Work.EL.RawPair.sideThrough hN R (p + (m : ℝ)) (q + (m' : ℝ))
      = Work.EL.RawPair.sideThrough hN R p q := by
  unfold Work.EL.RawPair.sideThrough
  have harc : Work.EL.arcLen (p + (m : ℝ)) (q + (m' : ℝ)) = Work.EL.arcLen p q := by
    unfold Work.EL.arcLen
    rw [show q + (m' : ℝ) - (p + (m : ℝ)) = (q - p) + ((m' - m : ℤ) : ℝ) by
        push_cast; ring,
      Int.fract_add_intCast]
  rw [harc]
  congr 1
  rw [show p + (m : ℝ) + Work.EL.arcLen p q / 2
      = (p + Work.EL.arcLen p q / 2) + (m : ℝ) by ring]
  exact Work.ELTop.rayPt_add_int hN (p + Work.EL.arcLen p q / 2) 2 m

/-! ## The main theorem -/

theorem cv_mem_arcSide_of_W0 {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) (Q : Work.ELPull.CoPair (Work.ELAssembly.hNcanOf d)) (I : ℝ × ℝ) (hI : Work.ELPull.IsUnwrappedArcOf Q I) (hW : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ I.2 I.1) : c ∈ Work.ELPull.arcSide (Work.ELAssembly.hNcanOf d) Q I.2 I.1 := by
  -- transport to the `Work.EL` vocabulary
  rw [cvside_diag_arcSide]
  have hLa : Work.EL.LandsN d.hN Q.a Q.y := (cvside_diag_landsN d Q.a Q.y).mp Q.lands_a
  have hLb : Work.EL.LandsN d.hN Q.b Q.y := (cvside_diag_landsN d Q.b Q.y).mp Q.lands_b
  let R : Work.EL.CoPair d.hN :=
    { toRawPair := ⟨Q.a, Q.b, Q.y⟩, lands_a := hLa, lands_b := hLb }
  by_cases hy : Q.y = d.z₁
  · -- **(2)** `Q.y = z₁`: the portrait at `z₁` and `hW` determine the arc, and the side
    -- is the far side of the `α`-pair
    have hpa : ∃ m : ℤ, Q.a = Work.EL.alpha1 + m ∨ Q.a = Work.EL.alpha2 + m :=
      eq_alpha_of_landsN_z1 d hzero (by rw [← hy]; exact hLa)
    have hpb : ∃ m : ℤ, Q.b = Work.EL.alpha1 + m ∨ Q.b = Work.EL.alpha2 + m :=
      eq_alpha_of_landsN_z1 d hzero (by rw [← hy]; exact hLb)
    rcases hI with ⟨hI1, hI2⟩ | ⟨hI1, hI2⟩
    · -- the arc fed to the pull-back is `(Q.a, Q.b)` (the far arc); `(I.2, I.1)` is the far arc
      have hI2' : I.2 = Q.a + Work.EL.arcLen Q.a Q.b := hI2
      have hm : Q.a + Work.EL.arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ) : ℝ) :=
        cvside_add_arcLen_eq Q.a Q.b
      have hu : ∃ m : ℤ, I.2 = Work.EL.alpha1 + m ∨ I.2 = Work.EL.alpha2 + m := by
        obtain ⟨m, hm' | hm'⟩ := hpb
        · refine ⟨m - ⌊Q.b - Q.a⌋, Or.inl ?_⟩
          rw [hI2', hm, hm']; push_cast; ring
        · refine ⟨m - ⌊Q.b - Q.a⌋, Or.inr ?_⟩
          rw [hI2', hm, hm']; push_cast; ring
      have hv : ∃ m : ℤ, I.1 = Work.EL.alpha1 + m ∨ I.1 = Work.EL.alpha2 + m := by
        rw [hI1]; exact hpa
      obtain ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩ := InArc_W0_orientation hu hv hW
      have hQa : ∃ k : ℤ, Q.a = Work.EL.alpha2 + (k : ℝ) := ⟨m₂, by rw [← hI1]; exact hm₂⟩
      have hQb : ∃ k : ℤ, Q.b = Work.EL.alpha1 + (k : ℝ) := by
        refine ⟨m₁ - (-⌊Q.b - Q.a⌋), ?_⟩
        have h := hm₁
        rw [hI2', hm] at h
        push_cast at h ⊢
        linarith
      have hcurve : Work.EL.RawPair.curve d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
          = Work.EL.pairCurve (alphaPairOf d) := by
        obtain ⟨k, hk⟩ := hQa
        obtain ⟨k', hk'⟩ := hQb
        have e1 : Work.EL.paramRay d.hN Q.a = Work.EL.paramRay d.hN Work.EL.alpha2 := by
          rw [hk]; exact Work.ELTop.paramRay_add_int d.hN Work.EL.alpha2 k
        have e2 : Work.EL.paramRay d.hN Q.b = Work.EL.paramRay d.hN Work.EL.alpha1 := by
          rw [hk']; exact Work.ELTop.paramRay_add_int d.hN Work.EL.alpha1 k'
        show Work.EL.paramRay d.hN Q.a ∪ {Q.y} ∪ Work.EL.paramRay d.hN Q.b
            = Work.EL.paramRay d.hN Work.EL.alpha1 ∪ {d.z₁} ∪ Work.EL.paramRay d.hN Work.EL.alpha2
        rw [e1, e2, hy]
        ext z; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
      have hρ : Work.EL.rayPt d.hN (I.2 + Work.EL.arcLen I.2 I.1 / 2) 2
          = Work.EL.rayPt d.hN (Work.EL.alpha1 + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2) 2 := by
        have harc : Work.EL.arcLen I.2 I.1 = Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 := by
          rw [hm₁, hm₂]; unfold Work.EL.arcLen
          rw [show Work.EL.alpha2 + (m₂ : ℝ) - (Work.EL.alpha1 + (m₁ : ℝ))
                = (Work.EL.alpha2 - Work.EL.alpha1) + ((m₂ - m₁ : ℤ) : ℝ) by push_cast; ring,
            Int.fract_add_intCast]
        rw [harc, hm₁]
        rw [show Work.EL.alpha1 + (m₁ : ℝ) + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2
              = (Work.EL.alpha1 + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2) + (m₁ : ℝ)
            by ring]
        exact Work.ELTop.rayPt_add_int d.hN _ 2 m₁
      simp only [Work.EL.RawPair.sideThrough]
      rw [hcurve, hρ]
      exact cv_mem_pairSide_alpha d
    · -- the arc fed to the pull-back is `(Q.b, Q.a)` (the near arc); `(I.2, I.1)` is the near arc
      have hI2' : I.2 = Q.b + Work.EL.arcLen Q.b Q.a := hI2
      have hm : Q.b + Work.EL.arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ) : ℝ) :=
        cvside_add_arcLen_eq Q.b Q.a
      have hu : ∃ m : ℤ, I.2 = Work.EL.alpha1 + m ∨ I.2 = Work.EL.alpha2 + m := by
        obtain ⟨m, hm' | hm'⟩ := hpa
        · refine ⟨m - ⌊Q.a - Q.b⌋, Or.inl ?_⟩
          rw [hI2', hm, hm']; push_cast; ring
        · refine ⟨m - ⌊Q.a - Q.b⌋, Or.inr ?_⟩
          rw [hI2', hm, hm']; push_cast; ring
      have hv : ∃ m : ℤ, I.1 = Work.EL.alpha1 + m ∨ I.1 = Work.EL.alpha2 + m := by
        rw [hI1]; exact hpb
      obtain ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩ := InArc_W0_orientation hu hv hW
      have hQa : ∃ k : ℤ, Q.a = Work.EL.alpha1 + (k : ℝ) := by
        refine ⟨m₁ - (-⌊Q.a - Q.b⌋), ?_⟩
        have h := hm₁
        rw [hI2', hm] at h
        push_cast at h ⊢
        linarith
      have hQb : ∃ k : ℤ, Q.b = Work.EL.alpha2 + (k : ℝ) := ⟨m₂, by rw [← hI1]; exact hm₂⟩
      have hcurve : Work.EL.RawPair.curve d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
          = Work.EL.pairCurve (alphaPairOf d) := by
        obtain ⟨k, hk⟩ := hQa
        obtain ⟨k', hk'⟩ := hQb
        have e1 : Work.EL.paramRay d.hN Q.a = Work.EL.paramRay d.hN Work.EL.alpha1 := by
          rw [hk]; exact Work.ELTop.paramRay_add_int d.hN Work.EL.alpha1 k
        have e2 : Work.EL.paramRay d.hN Q.b = Work.EL.paramRay d.hN Work.EL.alpha2 := by
          rw [hk']; exact Work.ELTop.paramRay_add_int d.hN Work.EL.alpha2 k'
        show Work.EL.paramRay d.hN Q.a ∪ {Q.y} ∪ Work.EL.paramRay d.hN Q.b
            = Work.EL.paramRay d.hN Work.EL.alpha1 ∪ {d.z₁} ∪ Work.EL.paramRay d.hN Work.EL.alpha2
        rw [e1, e2, hy]
      have hρ : Work.EL.rayPt d.hN (I.2 + Work.EL.arcLen I.2 I.1 / 2) 2
          = Work.EL.rayPt d.hN (Work.EL.alpha1 + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2) 2 := by
        have harc : Work.EL.arcLen I.2 I.1 = Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 := by
          rw [hm₁, hm₂]; unfold Work.EL.arcLen
          rw [show Work.EL.alpha2 + (m₂ : ℝ) - (Work.EL.alpha1 + (m₁ : ℝ))
                = (Work.EL.alpha2 - Work.EL.alpha1) + ((m₂ - m₁ : ℤ) : ℝ) by push_cast; ring,
            Int.fract_add_intCast]
        rw [harc, hm₁]
        rw [show Work.EL.alpha1 + (m₁ : ℝ) + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2
              = (Work.EL.alpha1 + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2) + (m₁ : ℝ)
            by ring]
        exact Work.ELTop.rayPt_add_int d.hN _ 2 m₁
      simp only [Work.EL.RawPair.sideThrough]
      rw [hcurve, hρ]
      exact cv_mem_pairSide_alpha d
  · -- **(1)** `Q.y ≠ z₁`: the curve of `Q` misses that of the `α`-pair, and the side of the
    -- `α`-pair is transported by `pairSide_subset_pairSide(Near)`
    have hdisj : Disjoint (Work.EL.pairCurve (alphaPairOf d)) (Work.EL.pairCurve R) :=
      pairCurve_disjoint_alpha d R (by rw [show R.y = Q.y from rfl]; exact hy)
    rcases hI with ⟨hI1, hI2⟩ | ⟨hI1, hI2⟩
    · -- `(I.2, I.1)` is the near arc of `Q`
      have hI2' : I.2 = Q.a + Work.EL.arcLen Q.a Q.b := hI2
      have hm : Q.a + Work.EL.arcLen Q.a Q.b = Q.b + ((-⌊Q.b - Q.a⌋ : ℤ) : ℝ) :=
        cvside_add_arcLen_eq Q.a Q.b
      have hside : Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) I.2 I.1
          = Work.EL.pairSideNear R := by
        rw [hI1, hI2', hm]
        have key : Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
              (Q.b + ((-⌊Q.b - Q.a⌋ : ℤ) : ℝ)) Q.a
            = Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) Q.b Q.a := by
          simpa using cvside_sideThrough_congr_arc d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
            Q.b Q.a (-⌊Q.b - Q.a⌋) 0
        rw [key]
        rfl
      have harc : ∀ θ : ℝ, Work.EL.InArc θ (alphaPairOf d).a (alphaPairOf d).b →
          Work.EL.InArc θ R.b (R.a + 1) := by
        intro θ hθ
        have h1 : Work.EL.InArc θ I.2 I.1 := hW θ hθ
        rw [hI1, hI2', hm] at h1
        have h2 : Work.EL.InArc θ Q.b Q.a :=
          (cvside_InArc_add_left_int θ Q.b Q.a (-⌊Q.b - Q.a⌋)).mp h1
        simpa using (Work.ELTop.InArc_right_add_int θ Q.b Q.a 1).mpr h2
      rw [hside]
      exact (Work.ELTop.pairSide_subset_pairSideNear d.hN Work.TopJordan.jordanForm
        (alphaPairOf d) R hdisj harc) (cv_mem_pairSide_alpha d)
    · -- `(I.2, I.1)` is the far arc of `Q`
      have hI2' : I.2 = Q.b + Work.EL.arcLen Q.b Q.a := hI2
      have hm : Q.b + Work.EL.arcLen Q.b Q.a = Q.a + ((-⌊Q.a - Q.b⌋ : ℤ) : ℝ) :=
        cvside_add_arcLen_eq Q.b Q.a
      have hside : Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) I.2 I.1
          = Work.EL.pairSide R := by
        rw [hI1, hI2', hm]
        have key : Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
              (Q.a + ((-⌊Q.a - Q.b⌋ : ℤ) : ℝ)) Q.b
            = Work.EL.RawPair.sideThrough d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair) Q.a Q.b := by
          simpa using cvside_sideThrough_congr_arc d.hN (⟨Q.a, Q.b, Q.y⟩ : Work.EL.RawPair)
            Q.a Q.b (-⌊Q.a - Q.b⌋) 0
        rw [key]
        rfl
      have harc : ∀ θ : ℝ, Work.EL.InArc θ (alphaPairOf d).a (alphaPairOf d).b →
          Work.EL.InArc θ R.a R.b := by
        intro θ hθ
        have h1 : Work.EL.InArc θ I.2 I.1 := hW θ hθ
        rw [hI1, hI2', hm] at h1
        exact (cvside_InArc_add_left_int θ Q.a Q.b (-⌊Q.a - Q.b⌋)).mp h1
      rw [hside]
      exact (Work.ELTop.pairSide_subset_pairSide d.hN Work.TopJordan.jordanForm
        (alphaPairOf d) R hdisj harc) (cv_mem_pairSide_alpha d)

end Work.ELAssembly
