import Mathlib
import Submission.Work.EpsW.countsWd
import Submission.Work.Drive.EpsFormSphere.Sideways
import Submission.Work.Drive.EpsFormSphere.slabArc_of_crossing
import Submission.Work.Drive.EpsFormSphere.count_bound_of_hS_hU
import Submission.Work.Drive.EpsFormSphere.frontier_swept_subset
import Submission.Work.Drive.EpsFormSphere.exists_inBoxSlab_near_of_face
import Submission.Work.Drive.EpsForm.distortionBound_one_le
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous
import Submission.Work.Drive.EpsForm.countingHalfEps_holds
import Submission.Work.Drive.EpsForm.encard_inter_sphereSet_lt_min

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- **The swept ball** of the slab design: the box with the part of the slab in front of the level
`lam` of the sweeping functional removed. -/
def sweptBall (s u h lam : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  {y : R3 | y ∈ Submission.PBox s c σ ∧ ¬ (y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ ℓ y < lam)}

/-- The wall of the swept ball: the part of the slab behind the level `lam`. -/
def slabWall (u h lam : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ) : Set R3 :=
  Work.Drive.EpsSphere.slabZ c σ u h ∩ {y : R3 | ℓ y < lam}

theorem sweptBall_eq_sdiff (s u h lam : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ) :
    sweptBall s u h lam c σ ℓ = Submission.PBox s c σ \ slabWall u h lam c σ ℓ := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h.1, h.2⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h.1, h.2⟩⟩

/-- **Pardon's box is open.** -/
theorem isOpen_PBox' (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    IsOpen (Submission.PBox s c σ) := by
  have h : Submission.PBox s c σ = {y : R3 | Submission.boxNorm c σ y < s} := by
    ext y; exact Submission.mem_PBox_iff s c σ y
  rw [h]
  exact isOpen_lt (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const

/-- **The trivial half of the frontier decomposition**: the frontier of the swept ball lies on the
frontier of the box or inside the box. -/
theorem frontier_sweptBall_subset_box (s u h lam : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ) :
    frontier (sweptBall s u h lam c σ ℓ) ⊆
      frontier (Submission.PBox s c σ) ∪ Submission.PBox s c σ := by
  intro x hx
  rw [sweptBall_eq_sdiff] at hx
  have hcl : x ∈ closure (Submission.PBox s c σ) := closure_mono sdiff_subset hx.1
  by_cases hxA : x ∈ Submission.PBox s c σ
  · exact Or.inr hxA
  · exact Or.inl ⟨hcl, fun h => hxA (interior_subset h)⟩

/-- **The frontier of the box is the box sphere.** -/
theorem frontier_PBox_subset_boxNorm (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    frontier (Submission.PBox s c σ) ⊆ {y : R3 | Submission.boxNorm c σ y = s} := by
  intro y hy
  have hcl : y ∈ closure (Submission.PBox s c σ) := frontier_subset_closure hy
  have hynotin : y ∉ Submission.PBox s c σ := by
    intro h
    rw [← (isOpen_PBox' s c σ).interior_eq] at h
    exact hy.2 h
  refine le_antisymm ?_ ?_
  · have hcont : Continuous (Submission.boxNorm c σ) :=
      Work.Topology.SphereSlicing.boxNorm_continuous c σ
    have hsub : Submission.PBox s c σ ⊆ Submission.boxNorm c σ ⁻¹' (Set.Iio s) :=
      fun z hz => (Submission.mem_PBox_iff s c σ z).mp hz
    have hmem := hcont.closure_preimage_subset (Set.Iio s) (closure_mono hsub hcl)
    rw [Set.mem_preimage, closure_Iio] at hmem
    exact hmem
  · by_contra hcon
    exact hynotin ((Submission.mem_PBox_iff s c σ y).mpr (not_le.mp hcon))

/-- **`encard` bookkeeping**: a set contained in a union is counted by the sum of the counts. -/
theorem encard_le_add_of_subset_union {A B C : Set ℝ} (h : A ⊆ B ∪ C) :
    (↑(Set.encard A) : ENNReal) ≤ (↑(Set.encard B) : ENNReal) + (↑(Set.encard C) : ENNReal) :=
  calc (↑(Set.encard A) : ENNReal) ≤ (↑(Set.encard (B ∪ C)) : ENNReal) :=
        ENat.toENNReal_mono (Set.encard_le_encard h)
    _ ≤ (↑(Set.encard B) : ENNReal) + (↑(Set.encard C) : ENNReal) :=
        le_trans (ENat.toENNReal_mono (Set.encard_union_le B C))
          (le_of_eq (ENat.toENNReal_add _ _))

open LeanEval.KnotTheory.PardonDistortion in
/-- **The count at a regular level of the sideways slab sweep.**

At a configuration carrying the crux's counting data, let `R = PBox s c σ \ (slabZ c σ u h ∩ {y | ℓ y < lam})` be the swept ball of the slab design.  Assume

* `hbound`, `hd`, `himg`, `hsmall`, `hSbound`, `hUbound` are the crux's hypotheses (distortion bound, prescribed image, `countConst * d < min p q`, and the two counts on the box sphere and on the cutting plane);
* `hatt` — **the thin-slab structure at every crossing of the cutting disc**: the parameters at which the knot lies in the slab *and* in the box form, near such a crossing, exactly an interval `Ioo a b` around it (maximal: no in-box slab point outside it), and the sweeping functional `ℓ` is strictly increasing along it.  For a small enough `h` this is the conclusion of `Work.Drive.EpsFormSphere.slabArc_of_crossing` (its monotonicity, upgraded to the maximal in-box component by `hcover`), and it is *the* hypothesis that bounds the number of times the knot meets the wall `{ℓ = lam}` (at most once per interval) and the slab faces (the interval's ends, which contribute at most one face point to the frontier unless the whole interval is behind the wall, giving two);
* `hcover` — every point of the knot inside the box and in the slab lies on the segment joining it to a crossing of the cutting disc *that stays inside the box and the slab* (this fails if a crossing of the plane lies on `∂PBox`; it is the general position the sweep must be built in);
* `hface` — the knot crosses the slab faces transversally (no tangential contact with a face, which would contribute an uncounted frontier point).

Then the knot meets the frontier of the swept ball in fewer than `min p q` points: at most `#(K ∩ ∂PBox) ≤ nS` on the box sphere, and at most `2` per in-box crossing (at most `nU` of them), giving `nS + 2 nU ≤ 150 d < min p q` (`Work.Drive.EpsFormSphere.count_bound_of_hS_hU`).  Composed with the slicing form of Pardon's Lemma 2 (`Work.EpsW.trace_inessential_of_slicing_of_countsWd`) and with `Work.Drive.EpsFormSphere.windingSpan_bot_or_top_of_trace_inessential`, this is the counting input of the design's `SideSweepData.dichotomy` field (P4). -/
theorem encard_frontier_inter_lt_min
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s u h lam : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) {ℓ : R3 →L[ℝ] ℝ}
    (hSbound : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Submission.boxNorm c σ (K.curve t) = s} ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hUbound : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u} ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))
    (hatt : ∀ t : ℝ, K.curve t ∈ Work.BoxShrink.Core.cutDisc s c σ u →
      ∃ h₀ a b : ℝ, 0 < h₀ ∧ h < h₀ ∧ a < t ∧ t < b ∧
        (∀ r ∈ Set.Ioo a b, K.curve r ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ K.curve r ∈ Submission.PBox s c σ) ∧
        (∀ r ∈ Set.Ico 0 (2 * Real.pi), (r < a ∨ b < r) → K.curve r ∈ Work.Drive.EpsSphere.slabZ c σ u h → K.curve r ∈ Submission.PBox s c σ → False) ∧
        ∀ r ∈ Set.Ioo a b, ∀ r' ∈ Set.Ioo a b, r < r' → ℓ (K.curve r) < ℓ (K.curve r'))
    (hcover : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) → K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h → K.curve t ∈ Submission.PBox s c σ → ∃ t' : ℝ, t' ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t' ∈ Work.BoxShrink.Core.cutDisc s c σ u ∧ ∀ r : ℝ, r ∈ Set.Icc (min t t') (max t t') → K.curve r ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ K.curve r ∈ Submission.PBox s c σ)
    (hface : ∀ r : ℝ, |K.curve r (σ 2) - (c (σ 2) + u)| = h → K.curve r ∈ Submission.PBox s c σ → (deriv K.curve r) (σ 2) ≠ 0) :
    Set.encard (Set.range K.curve ∩ frontier {y : R3 | y ∈ Submission.PBox s c σ ∧ ¬ (y ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ ℓ y < lam)}) < (Nat.min p q : ENNReal) := by
  classical
  show Set.encard (Set.range K.curve ∩ frontier (sweptBall s u h lam c σ ℓ)) <
    (Nat.min p q : ENNReal)
  -- ### the arithmetic
  have hd1 : 1 ≤ d := Work.Drive.EpsForm.distortionBound_one_le K d hbound
  have hminR : 150 * d < (Nat.min p q : ℝ) := by
    have h := hsmall
    rw [show Submission.countConst = (150 : ℝ) from rfl] at h
    exact h
  have hminpos : 0 < (Nat.min p q : ℝ) := by linarith
  have hkey : 75 * d + 4 < (Nat.min p q : ℝ) := by
    have h150 : (150 : ℝ) < (Nat.min p q : ℝ) := by linarith
    linarith
  -- ### the two counts
  have hencS :
      (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal) ≤ ENNReal.ofReal (75 * d) := by
    have h := hSbound
    rw [ten_mul_one_add_eps_div_eps] at h
    exact h
  have hencP :
      (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (sweptBall s u h lam c σ ℓ)}) : ENNReal) ≤ 4 := by
    set BadPath : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ frontier (sweptBall s u h lam c σ ℓ)}
      with hBadPath
    by_cases hpos : 0 < h
    · -- ### `h > 0`: the geometric case
      set T : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧ K.curve t ∈ Submission.PBox s c σ}
        with hT
      set Fset : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ |K.curve t (σ 2) - (c (σ 2) + u)| = h} with hFset
      set Wset : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ |K.curve t (σ 2) - (c (σ 2) + u)| < h ∧
          ℓ (K.curve t) = lam} with hWset
      have hBW : BadPath ⊆ Fset ∪ Wset := by
        intro t ht
        rw [hBadPath] at ht
        obtain ⟨htIco, htbox, htR⟩ := ht
        have hfr := frontier_swept_subset (s := s) (u := u) (h := h) (lam := lam)
          (c := c) (σ := σ) (ℓ := ℓ) hpos htR
        rcases hfr with hf | hf
        · have hmem : K.curve t ∈ interior (Submission.PBox s c σ) := by
            rw [(isOpen_PBox' s c σ).interior_eq]
            exact htbox
          exact absurd hmem hf.2
        · rcases hf with h | h
          · exact Or.inl (by rw [hFset]; exact ⟨htIco, htbox, h⟩)
          · exact Or.inr (by rw [hWset]; exact ⟨htIco, htbox, h.1, h.2⟩)
      by_cases hTne : T.Nonempty
      · -- ### there is an in-box slab arc
        obtain ⟨t₀, ht₀⟩ := hTne
        rw [hT] at ht₀
        obtain ⟨ht₀Ico, ht₀slab, ht₀box⟩ := ht₀
        obtain ⟨t', ht'Ico, ht'cut, -⟩ := hcover t₀ ht₀Ico ht₀slab ht₀box
        obtain ⟨h₀, a, b, hh₀, hhah, hat', ht'b, hAb, hBb, hCb⟩ := hatt t' ht'cut
        have hab : a < b := lt_trans hat' ht'b
        have hTsub : T ⊆ Set.Icc a b := by
          intro r hr
          rw [hT] at hr
          obtain ⟨hrIco, hrslab, hrbox⟩ := hr
          by_contra hcon
          rw [Set.mem_Icc, not_and_or] at hcon
          rcases hcon with hc | hc
          · exact hBb r hrIco (Or.inl (not_le.mp hc)) hrslab hrbox
          · exact hBb r hrIco (Or.inr (not_le.mp hc)) hrslab hrbox
        have hwall : ∀ r ∈ Set.Ioo a b, ∀ r' ∈ Set.Ioo a b,
            ℓ (K.curve r) = lam → ℓ (K.curve r') = lam → r = r' := by
          intro r hr r' hr' h1 h2
          rcases lt_trichotomy r r' with h | h | h
          · have hc := hCb r hr r' hr' h
            rw [h1, h2] at hc
            exact absurd hc (lt_irrefl lam)
          · exact h
          · have hc := hCb r' hr' r hr h
            rw [h1, h2] at hc
            exact absurd hc (lt_irrefl lam)
        obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
            Set.Ioo a b ∩ {r : ℝ | ℓ (K.curve r) = lam} ⊆ {c₀} := by
          by_cases hne : (Set.Ioo a b ∩ {r : ℝ | ℓ (K.curve r) = lam}).Nonempty
          · obtain ⟨r₀, hr₀⟩ := hne
            exact ⟨r₀, fun r hr => by
              rw [Set.mem_singleton_iff]
              exact hwall r hr.1 r₀ hr₀.1 hr.2 hr₀.2⟩
          · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ hne⟩
        have hFsub : Fset ⊆ insert a (insert b (insert 0 ({c₀} : Set ℝ))) := by
          intro t ht
          rw [hFset] at ht
          obtain ⟨htIco, htbox, htlev⟩ := ht
          rcases eq_or_ne t 0 with h0 | h0
          · rw [h0]; simp
          · have ht_pos : 0 < t := lt_of_le_of_ne htIco.1 (Ne.symm h0)
            have hnear : ∀ ε : ℝ, 0 < ε → ∃ r ∈ T, |r - t| < ε := by
              intro ε hε
              set δ : ℝ := min (min ε t) (2 * Real.pi - t) / 2 with hδ
              have hδpos : 0 < δ := by
                rw [hδ]
                have h1 : 0 < min (min ε t) (2 * Real.pi - t) :=
                  lt_min (lt_min hε ht_pos) (by linarith [htIco.2])
                positivity
              have hδε : δ ≤ ε := by
                rw [hδ]
                have h1 := min_le_left (min ε t) (2 * Real.pi - t)
                have h2 := min_le_left ε t
                linarith
              have hδt : δ ≤ t := by
                rw [hδ]
                have h1 := min_le_left (min ε t) (2 * Real.pi - t)
                have h2 := min_le_right ε t
                linarith
              have hδ2 : δ ≤ 2 * Real.pi - t := by
                rw [hδ]
                have h1 := min_le_right (min ε t) (2 * Real.pi - t)
                linarith
              obtain ⟨r, hdd, hrslab, hrbox⟩ :=
                exists_inBoxSlab_near_of_face (K := K) (c := c) (σ := σ) (u := u) (h := h)
                  (s := s) (t := t) hpos (hface t htlev htbox) htbox htlev δ hδpos
              refine ⟨r, ?_, ?_⟩
              · rw [hT]
                rw [abs_lt] at hdd
                exact ⟨⟨by linarith, by linarith⟩, hrslab, hrbox⟩
              · rw [abs_lt] at hdd ⊢
                exact ⟨by linarith, by linarith⟩
            have htcl : t ∈ closure T := by
              rw [Metric.mem_closure_iff]
              intro ε hε
              obtain ⟨r, hrT, hd⟩ := hnear ε hε
              exact ⟨r, hrT, by rw [Real.dist_eq, abs_sub_comm]; exact hd⟩
            have htin : t ∈ Set.Icc a b := by
              have h2 := closure_mono hTsub htcl
              rwa [closure_Icc] at h2
            have hnotin : t ∉ Set.Ioo a b := by
              intro hioo
              have hlt : |K.curve t (σ 2) - (c (σ 2) + u)| < h := (hAb t hioo).1
              rw [htlev] at hlt
              exact absurd hlt (lt_irrefl h)
            rcases Set.mem_Icc.mp htin with ⟨h1, h2⟩
            rcases eq_or_lt_of_le h1 with h | h
            · rw [← h]; simp
            · rcases eq_or_lt_of_le h2 with h' | h'
              · rw [h']; simp
              · exact absurd ⟨h, h'⟩ hnotin
        have hWsub : Wset ⊆ insert a (insert b (insert 0 ({c₀} : Set ℝ))) := by
          intro t ht
          rw [hWset] at ht
          obtain ⟨htIco, htbox, htlt, htlam⟩ := ht
          have htT : t ∈ T := by rw [hT]; exact ⟨htIco, htlt, htbox⟩
          have htab : t ∈ Set.Icc a b := hTsub htT
          rcases Set.mem_Icc.mp htab with ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with h | h
          · rw [← h]; simp
          · rcases eq_or_lt_of_le h2 with h' | h'
            · rw [h']; simp
            · have hmem : t ∈ Set.Ioo a b ∩ {r : ℝ | ℓ (K.curve r) = lam} :=
                ⟨⟨h, h'⟩, htlam⟩
              have hc := hc₀ hmem
              rw [Set.mem_singleton_iff] at hc
              rw [hc]; simp
        have hsub : BadPath ⊆ insert a (insert b (insert 0 ({c₀} : Set ℝ))) :=
          Set.Subset.trans hBW (Set.union_subset hFsub hWsub)
        have henc4 :
            (↑(Set.encard (insert a (insert b (insert 0 ({c₀} : Set ℝ))))) : ENNReal) ≤ 4 := by
          have h1 : Set.encard (insert a (insert b (insert 0 ({c₀} : Set ℝ)))) ≤ 4 := by
            calc Set.encard (insert a (insert b (insert 0 ({c₀} : Set ℝ))))
                ≤ Set.encard (insert b (insert 0 ({c₀} : Set ℝ))) + 1 :=
                  Set.encard_insert_le _ _
              _ ≤ (Set.encard (insert 0 ({c₀} : Set ℝ)) + 1) + 1 :=
                  add_le_add (Set.encard_insert_le (insert 0 ({c₀} : Set ℝ)) b) le_rfl
              _ ≤ ((Set.encard ({c₀} : Set ℝ) + 1) + 1) + 1 :=
                  add_le_add
                    (add_le_add (Set.encard_insert_le ({c₀} : Set ℝ) 0) le_rfl) le_rfl
              _ = 4 := by rw [Set.encard_singleton]; norm_num
          simpa using ENat.toENNReal_mono h1
        exact le_trans (ENat.toENNReal_mono (Set.encard_le_encard hsub)) henc4
      · -- ### there is no in-box slab point at all
        have hTe : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hTne
        have hT₀e : {t : ℝ | K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧
            K.curve t ∈ Submission.PBox s c σ} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          obtain ⟨htslab, htbox⟩ := ht
          have hmem : K.curve t ∈ Set.range K.curve := ⟨t, rfl⟩
          rw [Work.Drive.EpsForm.range_knot_eq_image_Ico K] at hmem
          obtain ⟨r, hrIco, hr⟩ := hmem
          have hrT : r ∈ T := by
            rw [hT]
            exact ⟨hrIco, by rw [hr]; exact htslab, by rw [hr]; exact htbox⟩
          rw [hTe] at hrT
          exact hrT
        have hF_empty : Fset = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rw [hFset] at ht
          obtain ⟨htIco, htbox, htlev⟩ := ht
          obtain ⟨r, -, hrslab, hrbox⟩ :=
            exists_inBoxSlab_near_of_face (K := K) (c := c) (σ := σ) (u := u) (h := h)
              (s := s) (t := t) hpos (hface t htlev htbox) htbox htlev 1 one_pos
          have hrT₀ : r ∈ {t : ℝ | K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h ∧
              K.curve t ∈ Submission.PBox s c σ} := ⟨hrslab, hrbox⟩
          rw [hT₀e] at hrT₀
          exact hrT₀
        have hW_empty : Wset = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rw [hWset] at ht
          obtain ⟨htIco, htbox, htlt, -⟩ := ht
          have hmem : t ∈ T := by rw [hT]; exact ⟨htIco, htlt, htbox⟩
          rw [hTe] at hmem
          exact hmem
        have hBe : BadPath = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rcases hBW ht with h | h
          · rw [hF_empty] at h; exact h
          · rw [hW_empty] at h; exact h
        rw [hBe, Set.encard_empty]
        simp
    · -- ### `h ≤ 0`: the slab is empty
      have hzero : Work.Drive.EpsSphere.slabZ c σ u h = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        have hlt : |y (σ 2) - (c (σ 2) + u)| < h := hy
        have h0 : (0 : ℝ) ≤ |y (σ 2) - (c (σ 2) + u)| := abs_nonneg _
        linarith
      have hBall : sweptBall s u h lam c σ ℓ = Submission.PBox s c σ := by
        ext y
        simp only [sweptBall, Set.mem_setOf_eq]
        rw [hzero]
        simp
      have hBe : BadPath = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ht
        rw [hBadPath] at ht
        obtain ⟨-, hbox, hfr⟩ := ht
        rw [hBall] at hfr
        have hmem : K.curve t ∈ interior (Submission.PBox s c σ) := by
          rw [(isOpen_PBox' s c σ).interior_eq]
          exact hbox
        exact absurd hmem hfr.2
      rw [hBe, Set.encard_empty]
      simp
  -- ### the box-sphere part of the frontier
  have hBad_sub :
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ frontier (sweptBall s u h lam c σ ℓ)} ⊆
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Submission.boxNorm c σ (K.curve t) = s} ∪
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
        K.curve t ∈ frontier (sweptBall s u h lam c σ ℓ)} := by
    intro t ht
    obtain ⟨htIco, htR⟩ := ht
    by_cases hbox : K.curve t ∈ Submission.PBox s c σ
    · exact Or.inr ⟨htIco, hbox, htR⟩
    · refine Or.inl ⟨htIco, ?_⟩
      rcases frontier_sweptBall_subset_box s u h lam c σ ℓ htR with hf | hf
      · exact frontier_PBox_subset_boxNorm s c σ hf
      · exact absurd hf hbox
  have harith : ENNReal.ofReal (75 * d) + (4 : ENNReal) < (Nat.min p q : ENNReal) := by
    have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) := by simp
    rw [← h4, ← ENNReal.ofReal_add (by positivity) (by norm_num),
      ← ENNReal.ofReal_natCast (Nat.min p q)]
    exact (ENNReal.ofReal_lt_ofReal_iff hminpos).mpr hkey
  -- ### assembly
  have hstep1 :
      (↑(Set.encard (Set.range K.curve ∩ frontier (sweptBall s u h lam c σ ℓ))) : ENNReal) ≤
      (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ frontier (sweptBall s u h lam c σ ℓ)}) : ENNReal) :=
    ENat.toENNReal_mono (Work.Drive.EpsForm.encard_range_inter_le_param K _)
  have hstep2 := encard_le_add_of_subset_union hBad_sub
  have hfinal : (↑(Set.encard (Set.range K.curve ∩ frontier (sweptBall s u h lam c σ ℓ))) : ENNReal) <
      (Nat.min p q : ENNReal) :=
    lt_of_le_of_lt (le_trans hstep1 (le_trans hstep2 (add_le_add hencS hencP))) harith
  exact hfinal

end

end Work.Drive.EpsFormSphere
