import Mathlib
import Submission.Work.Drive.pairMeet2
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.exists_meet3Data_of_good_family
import Submission.Work.Drive.even_ncard_pairMeetBdry

/-!
# The weighted chart-shift of the symmetric pair map: T1/T3 on a compact set

`Submission/Work/Drive/even_ncard_pairMeetBdry2.lean` reduces the collapse count to the two
genericity fields of the **symmetric** pair map `Work.Drive.pairDiff2` (both chart blocks `s`-dependent):

* `hreg`: the `x`-derivative of the pair map is onto at every zero of the box;
* `hface`: every boundary zero lies on *exactly one* face coordinate, and the derivative restricted
  to that face is onto.

Here those two fields are produced for the **weighted chart-shift family**

> `E t s u = E₀ s u + w s • unpackFst t`,  `E' t s u = E'₀ s u + w s • unpackSnd t`,

i.e. the two chart blocks are both shifted by the two blocks of the parameter `t ∈ ℝ⁸`, weighted by a
function `w` of the family parameter `s = ftS x`.  The weight is what makes the perturbation vanish at
the two ends `s ∈ {0,1}` (take `w = σ (1-σ)`) while remaining effective in the interior, and it is the
reason the statement is *local in `K`*: at a point `x` of `K` the shift enters through `w (ftS x)`, so
the parameter-derivative is onto exactly when `w (ftS x) ≠ 0` — the hypothesis `hwne` (plus `hK`).

The whole proof is a single application of the merged genericity theorem
`Work.Drive.exists_forall_good_face_and_notMem_family` (parametric Sard + face-restricted Sard +
avoidance of the two-face skeleton, all at one parameter), with

* `Φ (p, z) = pairDiff2 (fun s u => E₀ s u + w s • unpackFst p) (fun s u => E'₀ s u + w s • unpackSnd p)
  V₀ W₀ z`, which is jointly `C^∞` (`contDiff_pairDiff2_shiftFamily` below);
* the two-face pieces of `K` (`TFid`, `TFdir`, `TFbase`, `TFcov` of
  `Submission/Work/Drive/exists_meet3Data_of_good_family.lean`, which is where the `Amb 8` skeleton
  was built) as the lower-dimensional family, so that the avoidance clause rules out a second face
  coordinate at a boundary zero;
* the parameter-derivative surjectivity hypothesis, which is
  `Work.Drive.surjective_fderiv_pairDiff2_weightedShift`: the value of `pairDiff2` at a *fixed* point
  of the nine-box sees the family only through the values at `(ftS x, ftU x)`, so the `s`-dependent
  weight and the constant weight `w (ftS x)` give the same function of the parameter.

All declarations here are `sorry`-free and rest on `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology

noncomputable section

/-! ## Joint smoothness of the shifted pair family -/

/-- **Joint smoothness of `(p, z) ↦ pairDiff2 (E₀ + w • unpackFst p) (E'₀ + w • unpackSnd p) V₀ W₀ z`.**

Since the family is the *pair* of chart blocks shifted by the two blocks of the parameter, the
smoothness in `(p, z)` is the smoothness of `E₀ (ftS z) (ftU z) + w (ftS z) • unpackFst p − V₀ (ftY z)`
and its companions; `unpackFst`/`unpackSnd` are continuous linear maps, and `pair44` of two smooth
`ℝ⁴`-valued maps is smooth (`Work.Drive.contDiff_pair44`). -/
lemma contDiff_pairDiff2_shiftFamily
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ)
    (hE₀ : ContDiff ℝ Ctop (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ Ctop (Function.uncurry E'₀))
    (hV₀ : ContDiff ℝ Ctop V₀) (hW₀ : ContDiff ℝ Ctop W₀) (hw : ContDiff ℝ Ctop w) :
    ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
        (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2) := by
  have hsu : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      ((ftS q.2, ftU q.2) : ℝ × EuclideanSpace ℝ (Fin 2))) := by
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => q.2 0)
      fun_prop
    · show ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
        WithLp.toLp 2 (fun i : Fin 2 => q.2 ⟨1 + i.val, by omega⟩))
      fun_prop
  have hY : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => ftY q.2) := by
    show ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨3 + i.val, by omega⟩))
    fun_prop
  have hZ : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => ftZ q.2) := by
    show ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨6 + i.val, by omega⟩))
    fun_prop
  have hws : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => w (ftS q.2)) := by
    refine hw.comp ?_
    show ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => q.2 0)
    fun_prop
  have huf : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => unpackFst q.1) :=
    unpackFst.contDiff.comp contDiff_fst
  have hus : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => unpackSnd q.1) :=
    unpackSnd.contDiff.comp contDiff_fst
  have h1 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => E₀ (ftS q.2) (ftU q.2)) :=
    hE₀.comp hsu
  have h2 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => E'₀ (ftS q.2) (ftU q.2)) :=
    hE'₀.comp hsu
  have h3 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => V₀ (ftY q.2)) :=
    hV₀.comp hY
  have h4 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 => W₀ (ftZ q.2)) :=
    hW₀.comp hZ
  have h5 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      w (ftS q.2) • unpackFst q.1) := hws.smul huf
  have h6 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      w (ftS q.2) • unpackSnd q.1) := hws.smul hus
  simp only [pairDiff2]
  exact PMB.contDiff_pair44 ((h1.add h5).sub h3) ((h2.add h6).sub h4)

/-! ## The parameter-derivative of the weighted shift -/

/-- **The value of the shifted pair family sees the parameter only through `w (ftS z)`.**

At a fixed point `z` of the nine-box the family is evaluated at `(ftS z, ftU z)`, so the `s`-dependent
weight `w s` of the shift can be replaced by the constant `w (ftS z)`.  This is what allows the
`hsurj` of the merged genericity theorem to be discharged by
`Work.Drive.surjective_fderiv_pairDiff2_weightedShift`. -/
lemma shiftFamily_apply_eq_weightedShift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (z : Amb 8) :
    (fun p' : EuclideanSpace ℝ (Fin 8) =>
        pairDiff2 (fun s u => E₀ s u + w s • unpackFst p')
          (fun s u => E'₀ s u + w s • unpackSnd p') V₀ W₀ z)
      = (fun t : EuclideanSpace ℝ (Fin 8) =>
        pairDiff2 (fun s u => E₀ s u + w (ftS z) • unpackFst t)
          (fun s u => E'₀ s u + w (ftS z) • unpackSnd t) V₀ W₀ z) := by
  funext p'
  simp only [pairDiff2]

/-! ## The genericity theorem -/

theorem exists_pairDiff2_good_shift
    (E₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E'₀ : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V₀ W₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hE₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E₀))
    (hE'₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'₀))
    (hV₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V₀)
    (hW₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W₀)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwne : ∀ x ∈ K, w (Work.Drive.ftS x) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < ε ∧
      (∀ x ∈ K, Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
          (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V₀ W₀ x = 0 →
        Function.Surjective (fderiv ℝ (Work.Drive.pairDiff2
          (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
          (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V₀ W₀) x)) ∧
      (∀ x ∈ K, Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
          (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V₀ W₀ x = 0 →
        x ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
            fderiv ℝ (Work.Drive.pairDiff2 (fun s u => E₀ s u + w s • Work.Drive.unpackFst t)
              (fun s u => E'₀ s u + w s • Work.Drive.unpackSnd t) V₀ W₀) x v.1)) := by
  classical
  -- ## the jointly smooth family of the merged theorem
  have hΦ : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
      pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
        (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2) :=
    contDiff_pairDiff2_shiftFamily E₀ E'₀ V₀ W₀ w hE₀ hE'₀ hV₀ hW₀ hw
  -- ## the parameter-derivative is onto at every base point of `K`
  have hsurj : ∀ (p : EuclideanSpace ℝ (Fin 8)) (z : Amb 8), ‖p‖ < ε →
      (z ∈ K ∨ ∃ i : TFid,
        z ∈ (fun l : TFdir i => TFbase i + (l : Amb 8)) '' (TFcov K i)) →
      (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
        pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
          (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2) (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin 8) =>
        (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
          pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
            (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2) (p', z)) p) := by
    intro p z _ hzd _
    have hzK : z ∈ K := hzd.elim id (fun ⟨i, l, hl, hlz⟩ => by rw [← hlz]; exact hl)
    show Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin 8) =>
        pairDiff2 (fun s u => E₀ s u + w s • unpackFst p')
          (fun s u => E'₀ s u + w s • unpackSnd p') V₀ W₀ z) p)
    rw [shiftFamily_apply_eq_weightedShift E₀ E'₀ V₀ W₀ w z]
    exact surjective_fderiv_pairDiff2_weightedShift E₀ E'₀ V₀ W₀ w p z (hwne z hzK)
  -- ## one application of the merged genericity theorem
  obtain ⟨p, hpnorm, hgood, hface, havoid⟩ :=
    exists_forall_good_face_and_notMem_family 8 8 K hK TFid
      (fun t => ↥(TFdir t)) (fun t => TFdir_finrank_lt t)
      (fun t => fun l : TFdir t => TFbase t + (l : Amb 8))
      (fun t => contDiff_TFparam t)
      (fun t => TFcov K t) (fun t => TFcov_isCompact K hK t)
      (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
        pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
          (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2)
      hΦ ε hε hsurj
  refine ⟨p, hpnorm, ?_, ?_⟩
  · -- ### the regularity clause
    intro x hx hzero
    exact hgood x hx hzero
  · -- ### the face clause
    intro x hx hzero hxbd
    rw [Submission.Drive.unitBoxBdry] at hxbd
    obtain ⟨hbox, i, hi⟩ := hxbd
    have hsurji := hface i x hx hzero hi
    -- no *second* face coordinate: that would put `x` on a two-face piece of `K`
    have hnot2 : ∀ j : Fin 9, j ≠ i → ¬ (x j = 0 ∨ x j = 1) := by
      intro j hj hb
      obtain ⟨t, l, hl, hlx⟩ := TFcov_cover K hx ⟨i, j, hj.symm, hi, hb⟩
      have hΦx : (fun q : EuclideanSpace ℝ (Fin 8) × Amb 8 =>
          pairDiff2 (fun s u => E₀ s u + w s • unpackFst q.1)
            (fun s u => E'₀ s u + w s • unpackSnd q.1) V₀ W₀ q.2) (p, x) = 0 := hzero
      exact havoid t l hl (by rw [hlx]; exact hΦx)
    refine ⟨i, hi, ?_, ?_⟩
    · intro j hj
      have hxj := hbox j
      have h0 : x j ≠ 0 := fun h => hnot2 j hj (Or.inl h)
      have h1 : x j ≠ 1 := fun h => hnot2 j hj (Or.inr h)
      exact ⟨lt_of_le_of_ne hxj.1 (Ne.symm h0), lt_of_le_of_ne hxj.2 h1⟩
    · exact hsurji

end

end Work.Drive
