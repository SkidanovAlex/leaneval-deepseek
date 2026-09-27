import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.blockReduction
import Submission.Work.Drive.N2.levelSeparatingMap_of_blocks
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.blockSkeleton
import Submission.Work.Drive.N2.bandLaw
import Submission.Work.Drive.N2.collarDrawing_local
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2.roundConfigPath
import Submission.Work.Drive.N2.roundConfigPictureGlobal
import Submission.Work.Drive.N2.pictureOfConfig
import Submission.Work.Drive.N2.reparametrisationIsotopy
import Submission.Work.Drive.N2.orientationFlipIsotopy
import Submission.Work.Drive.N2.arcRigidity
import Submission.Work.Drive.N2pc.exists_localLift
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.isLevelIsotopy_windowMovie
import Submission.Work.Drive.N2C.isLevelIsotopy_transport
import Submission.Work.Drive.N2C.levelCurves_transport
import Submission.Work.Drive.N2C.levelCurves_reverse
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2C.gapDrawing_of_certifiedEnds
/-!
# C2: the gap drawings of **certified** windows (the compact `n = 2` movie)

`Work.Drive.N2C.exists_gapDrawings_of_certifiedWindows` is statement **C2** of
`N2Lead/NOTES_LEAD_coherentWindows.md` §4 (Tier C): the parked drawings `gG` of the `n + 1`
critical-free gap bands of a strictly monotone skeleton `s`, with their rows on
`Work.Drive.N2.blockSet` and the two collar agreements with the window drawings `gw`.

## The proof

Write `s' := s (Fin.castSucc j)`, `s'' := s (Fin.succ j)` for the two critical values bounding the
`j`-th gap.

* **The two end gaps are value-empty.**  `gapValueBand s η 0 = Ioo (s 0 - η) (s 0 - η/2)` lies below
  `min f = s 0` (`hlo`), and the last gap `Ioo (s (last n) - η/2, s (last n) + η/2)'s lower end is
  above `max f` (`hhi`); so on both the `GoodDrawingOn` row is vacuous (`good_of_empty`) and so is the
  one collar agreement that would involve them (`hempty_zero`, `hempty_last`, `hempty_block0`,
  `hempty_block2`).
* **An inner gap `j` with `j + 1 < n` is the certified gap of `C1`.**  Instantiate
  `Work.Drive.N2C.gapDrawing_of_certifiedEnds` with the parameter table of the design,
  `lo' = s' + η/3`, `lo = s' + η/2`, `h₁ = s' + η`, `u₁ = s' + 3η/2`, `m₁ = s' + 2η`,
  `m₂ = s'' - 2η`, `u₂ = s'' - 3η/2`, `h₂ = s'' - η`, `hi = s'' - η/2`, `hi' = s'' - η/3`, with
  * the flow law on `Icc lo' hi'` from `Work.Drive.N2.bandLaw` together with `hKval` (the obstacles
    `K` are half an `η/4`-neighbourhood away from each critical value, hence avoid the closed band
    `Icc (s' + η/3) (s'' - η/3)`);
  * the regularity of that band from `hcrit` (no critical value lies strictly between `s'` and
    `s''`);
  * `hg₁`, `hg₂` by `.mono` from `hgw` (the window bands `Ioo (s j ∓ 2η)` contain the wider end
    bands `Ioo lo' m₁`, `Ioo m₂ hi'`);
  * `hc₁`, `hc₂` the certificates `hcertHi j`, `hcertLo (j+1)` at the levels `u₁ = s j + 3η/2`,
    `u₂ = s (j+1) - 3η/2`.
  `C1` delivers a good drawing of `Ioo lo hi = gapValueBand s η (j+1)` which agrees with `gw j` on
  `(lo, h₁) = blockSet s η (j,2)` and with `gw (j+1)` on `(h₂, hi) = blockSet s η (j+1, 0)`.
* **The family `gG`.**  `gG 0` and `gG (last n)` are arbitrary (their bands are value-empty);
  `gG (Fin.succ j)` is the `C1` drawing of the gap `j` when `j + 1 < n` and arbitrary otherwise.
  The two agreement rows are then exactly the two clauses of the `C1` drawing, transported along
  the index identifications `Fin.castSucc j = Fin.succ (Fin.pred ...)` and
  `(⟨j.1 + 1, _⟩ : Fin n) = j`.
-/

namespace Work.Drive.N2C

theorem exists_gapDrawings_of_certifiedWindows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {n : ℕ} (hn : 0 < n) {f : M → ℝ}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f)
    (hfm : Work.Drive.Morse.IsMorseDistinct f)
    {s : Fin (n + 1) → ℝ} (hs : StrictMono s) {η : ℝ} (hη : 0 < η)
    (hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j))
    (hlo : ∀ x : M, s 0 ≤ f x)
    (hhi : ∀ x : M, f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩))
    {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (((modelWithCornersSelf ℝ ℝ)).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    {K : Set M} (hKcl : IsClosed K)
    (hlaw : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ K) → f (Φ (t, y)) = f y + t)
    (hKval : ∀ y : M, y ∈ K → ∃ j : Fin n, |f y - s (Fin.castSucc j)| < η / 4)
    (hcrit : ∀ t : ℝ, (∃ x : M, Work.Drive.Morse.IsCritical f x ∧ f x = t) ↔
      ∃ j : Fin n, t = s (Fin.castSucc j))
    (gw : Fin n → M → EuclideanSpace ℝ (Fin 3))
    (hgw : ∀ j : Fin n, Work.Drive.N2.GoodDrawingOn f
      (Set.Ioo (s (Fin.castSucc j) - 2 * η) (s (Fin.castSucc j) + 2 * η)) (gw j))
    (hcertLo : ∀ j : Fin n, Work.Drive.N2C.IsCertifiedAt f (s (Fin.castSucc j) - 3 * η / 2) (gw j))
    (hcertHi : ∀ j : Fin n, Work.Drive.N2C.IsCertifiedAt f (s (Fin.castSucc j) + 3 * η / 2) (gw j)) :
    ∃ gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin (n + 1), Work.Drive.N2.GoodDrawingOn f
        (Work.Drive.N2.gapValueBand s η j) (gG j)) ∧
      (∀ (j : Fin n) (x : M), f x ∈ Work.Drive.N2.blockSet s η (j, 0) →
        gw j x = gG (Fin.castSucc j) x) ∧
      (∀ (j : Fin n) (x : M), f x ∈ Work.Drive.N2.blockSet s η (j, 2) →
        gw j x = gG (Fin.succ j) x) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  -- ## Step 0: the value-empty bands
  have hcc0 : (Fin.castSucc (0 : Fin n) : Fin (n + 1)) = 0 := by ext; simp
  have hccLast : ∀ (i : Fin n), i.1 + 1 = n →
      Fin.castSucc i = (Fin.castSucc ⟨n - 1, by omega⟩ : Fin (n + 1)) := by
    intro i hi
    ext
    simp only [Fin.val_castSucc]
    omega
  have hempty_zero : ∀ x : M, f x ∉ Work.Drive.N2.gapValueBand s η 0 := by
    intro x hx
    rw [Work.Drive.N2.gapValueBand_zero] at hx
    have h := hlo x
    simp only [Set.mem_Ioo] at hx
    linarith [hx.2, hη]
  have hempty_last : ∀ (i : Fin n), i.1 + 1 = n → ∀ x : M,
      f x ∉ Work.Drive.N2.gapValueBand s η (Fin.succ i) := by
    intro i hi x hx
    rw [Work.Drive.N2.gapValueBand_succ] at hx
    have h := hhi x
    rw [← hccLast i hi] at h
    simp only [Set.mem_Ioo] at hx
    linarith [hx.1, h, hη]
  have hempty_block0 : ∀ x : M, f x ∉ Work.Drive.N2.blockSet s η ((0 : Fin n), 0) := by
    intro x hx
    rw [Work.Drive.N2.blockSet_zero] at hx
    have h := hlo x
    rw [← hcc0] at h
    simp only [Set.mem_Ioo] at hx
    linarith [hx.2, hη]
  have hempty_block2 : ∀ (j : Fin n), j.1 + 1 = n → ∀ x : M,
      f x ∉ Work.Drive.N2.blockSet s η (j, 2) := by
    intro j hj x hx
    rw [Work.Drive.N2.blockSet_two] at hx
    have h := hhi x
    rw [← hccLast j hj] at h
    simp only [Set.mem_Ioo] at hx
    linarith [hx.1, h, hη]
  have good_of_empty : ∀ (A : Set ℝ) (g : M → EuclideanSpace ℝ (Fin 3)),
      (∀ x : M, f x ∉ A) → Work.Drive.N2.GoodDrawingOn f A g := by
    intro A g h
    exact ⟨fun x hx => absurd hx (h x), fun x hx => absurd hx (h x),
      fun x _ hx => absurd hx (h x)⟩
  -- ## Step 1: the certified drawing of each inner gap
  have hdraw : ∀ (i : Fin n) (hi : i.1 + 1 < n), ∃ G : M → EuclideanSpace ℝ (Fin 3),
      Work.Drive.N2.GoodDrawingOn f (Work.Drive.N2.gapValueBand s η (Fin.succ i)) G ∧
      (∀ x : M, f x ∈ Work.Drive.N2.blockSet s η (i, 2) → gw i x = G x) ∧
      (∀ x : M, f x ∈ Work.Drive.N2.blockSet s η (⟨i.1 + 1, hi⟩, 0) →
        gw ⟨i.1 + 1, hi⟩ x = G x) := by
    intro i hi
    set sl : ℝ := s (Fin.castSucc i) with hsl
    set su : ℝ := s (Fin.succ i) with hsu
    have hgap_i : sl + 4 * η < su := by rw [hsl, hsu]; exact hgap i
    have hbase : s (Fin.castSucc ⟨i.1 + 1, hi⟩) = su := by
      rw [hsu, ← Work.Drive.N2.fin_succ_eq_castSucc hi]
    -- the obstacles avoid the closed band
    have hKval' : ∀ y ∈ K, f y ∉ Set.Icc (sl + η / 3) (su - η / 3) := by
      intro y hy hmem
      obtain ⟨j, hj⟩ := hKval y hy
      have habs := abs_lt.mp hj
      by_cases hji : (j : ℕ) ≤ (i : ℕ)
      · have hle : s (Fin.castSucc j) ≤ sl := by
          rw [hsl]
          exact hs.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_iff_val_le_val.mpr hji))
        linarith [hle, habs.2, hmem.1, hη]
      · have hji' : (i : ℕ) < (j : ℕ) := by omega
        have hle : su ≤ s (Fin.castSucc j) := by
          rw [hsu]
          refine hs.monotone ?_
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        linarith [hle, habs.1, hmem.2, hη]
    have hΦcont : ∀ x : M, Continuous (fun t : ℝ => Φ (t, x)) := fun x =>
      hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
    have hlaw' : ∀ (y : M) (t : ℝ), f y ∈ Set.Icc (sl + η / 3) (su - η / 3) →
        f y + t ∈ Set.Icc (sl + η / 3) (su - η / 3) → f (Φ (t, y)) = f y + t := by
      intro y t h1 h2
      exact (Work.Drive.N2.bandLaw (B := K) (K := K) (a := sl + η / 3) (b := su - η / 3)
        (fun _ hb => hb) hKcl hKval' hf.continuous hΦcont hΦ0 hΦcomp hlaw h1 h2).2
    have hreg' : ∀ x : M, f x ∈ Set.Icc (sl + η / 3) (su - η / 3) →
        ¬ Work.Drive.Morse.IsCritical f x := by
      intro x hx hcritx
      obtain ⟨j, hj⟩ := (hcrit (f x)).mp ⟨x, hcritx, rfl⟩
      by_cases hji : (j : ℕ) ≤ (i : ℕ)
      · have hle : s (Fin.castSucc j) ≤ sl := by
          rw [hsl]
          exact hs.monotone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_iff_val_le_val.mpr hji))
        linarith [hle, hx.1, hη]
      · have hji' : (i : ℕ) < (j : ℕ) := by omega
        have hle : su ≤ s (Fin.castSucc j) := by
          rw [hsu]
          refine hs.monotone ?_
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        linarith [hle, hx.2, hη]
    have hsub₁ : Set.Ioo (sl + η / 3) (sl + 2 * η) ⊆
        Set.Ioo (s (Fin.castSucc i) - 2 * η) (s (Fin.castSucc i) + 2 * η) := by
      intro t ht
      rw [hsl] at ht
      simp only [Set.mem_Ioo] at ht ⊢
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsub₂ : Set.Ioo (su - 2 * η) (su - η / 3) ⊆
        Set.Ioo (s (Fin.castSucc ⟨i.1 + 1, hi⟩) - 2 * η)
          (s (Fin.castSucc ⟨i.1 + 1, hi⟩) + 2 * η) := by
      intro t ht
      rw [← hbase] at ht
      simp only [Set.mem_Ioo] at ht ⊢
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hg₁ : Work.Drive.N2.GoodDrawingOn f (Set.Ioo (sl + η / 3) (sl + 2 * η)) (gw i) :=
      (hgw i).mono hsub₁
    have hg₂ : Work.Drive.N2.GoodDrawingOn f (Set.Ioo (su - 2 * η) (su - η / 3))
        (gw ⟨i.1 + 1, hi⟩) := (hgw ⟨i.1 + 1, hi⟩).mono hsub₂
    have hc₁ : Work.Drive.N2C.IsCertifiedAt f (sl + 3 * η / 2) (gw i) := by
      rw [hsl]
      exact hcertHi i
    have hc₂ : Work.Drive.N2C.IsCertifiedAt f (su - 3 * η / 2) (gw ⟨i.1 + 1, hi⟩) := by
      have h := hcertLo ⟨i.1 + 1, hi⟩
      rwa [hbase] at h
    have hord : sl + η / 3 < sl + η / 2 ∧ sl + η / 2 < sl + η ∧ sl + η < sl + 3 * η / 2 ∧
        sl + 3 * η / 2 < sl + 2 * η ∧ sl + 2 * η ≤ su - 2 * η ∧ su - 2 * η < su - 3 * η / 2 ∧
        su - 3 * η / 2 < su - η ∧ su - η < su - η / 2 ∧ su - η / 2 < su - η / 3 := by
      refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩
    obtain ⟨G, hG1, hG2, hG3⟩ := Work.Drive.N2C.gapDrawing_of_certifiedEnds
      (f := f) (Φ := Φ) (lo' := sl + η / 3) (lo := sl + η / 2) (h₁ := sl + η)
      (u₁ := sl + 3 * η / 2) (m₁ := sl + 2 * η) (m₂ := su - 2 * η) (u₂ := su - 3 * η / 2)
      (h₂ := su - η) (hi := su - η / 2) (hi' := su - η / 3)
      hf hΦsm hΦ0 hΦcomp hord hlaw' hreg' hg₁ hg₂ hc₁ hc₂
    refine ⟨G, ?_, ?_, ?_⟩
    · rwa [Work.Drive.N2.gapValueBand_succ]
    · intro x hx
      refine (hG2 x ?_).symm
      rw [Work.Drive.N2.blockSet_two] at hx
      simp only [Set.mem_Ioo] at hx ⊢
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro x hx
      refine (hG3 x ?_).symm
      rw [Work.Drive.N2.blockSet_zero] at hx
      rw [← hbase]
      simp only [Set.mem_Ioo] at hx ⊢
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  choose Gfun hGfun using hdraw
  -- ## Step 2: the family `gG`
  let gG : Fin (n + 1) → M → EuclideanSpace ℝ (Fin 3) :=
    Fin.cases (fun _ : M => 0)
      (fun i : Fin n => if h : i.1 + 1 < n then Gfun i h else (fun _ : M => 0))
  have gG_zero : gG 0 = (fun _ : M => 0) := by
    show gG 0 = (fun _ : M => 0)
    dsimp only [gG]
    rw [Fin.cases_zero]
  have gG_succ : ∀ (i : Fin n) (h : i.1 + 1 < n), gG (Fin.succ i) = Gfun i h := by
    intro i h
    show gG (Fin.succ i) = Gfun i h
    dsimp only [gG]
    rw [Fin.cases_succ, dif_pos h]
  have gG_junk : ∀ (i : Fin n), ¬ (i.1 + 1 < n) → gG (Fin.succ i) = (fun _ : M => 0) := by
    intro i h
    show gG (Fin.succ i) = (fun _ : M => 0)
    dsimp only [gG]
    rw [Fin.cases_succ, dif_neg h]
  have exists_succ : ∀ j : Fin (n + 1), j ≠ 0 → ∃ i : Fin n, Fin.succ i = j :=
    fun j hj => ⟨Fin.pred j hj, Fin.succ_pred j hj⟩
  have decomp : ∀ (j : Fin n), j ≠ 0 → ∃ (i : Fin n) (hi : i.1 + 1 < n),
      Fin.castSucc j = Fin.succ i := by
    intro j hj
    have hj' : (Fin.castSucc j : Fin (n + 1)) ≠ 0 := by
      intro h
      exact hj (Fin.ext (by simpa using congrArg Fin.val h))
    refine ⟨Fin.pred (Fin.castSucc j) hj', ?_, ?_⟩
    · have h := congrArg Fin.val (Fin.succ_pred (Fin.castSucc j) hj')
      simp only [Fin.val_succ, Fin.val_castSucc] at h
      omega
    · exact (Fin.succ_pred (Fin.castSucc j) hj').symm
  refine ⟨gG, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · subst hj
      rw [gG_zero]
      exact good_of_empty _ _ hempty_zero
    · obtain ⟨i, rfl⟩ := exists_succ j hj
      by_cases hi : i.1 + 1 < n
      · rw [gG_succ i hi]
        exact (hGfun i hi).1
      · rw [gG_junk i hi]
        exact good_of_empty _ _ (hempty_last i (by omega))
  · intro j x hx
    by_cases hj : j = 0
    · subst hj
      exact absurd hx (hempty_block0 x)
    · obtain ⟨i, hi, hcast⟩ := decomp j hj
      have hidx : (⟨i.1 + 1, hi⟩ : Fin n) = j := by
        apply Fin.ext
        have h2 : Fin.castSucc (⟨i.1 + 1, hi⟩ : Fin n) = Fin.castSucc j := by
          rw [← Work.Drive.N2.fin_succ_eq_castSucc hi, ← hcast]
        simpa using congrArg Fin.val h2
      have hgj : gG (Fin.castSucc j) = Gfun i hi := by rw [hcast, gG_succ i hi]
      rw [hgj]
      have hspec := (hGfun i hi).2.2
      rw [hidx] at hspec
      exact hspec x hx
  · intro j x hx
    by_cases hj : j.1 + 1 < n
    · rw [gG_succ j hj]
      exact (hGfun j hj).2.1 x hx
    · have hlast : j.1 + 1 = n := by omega
      rw [gG_junk j hj]
      exact absurd hx (hempty_block2 j hlast x)

end Work.Drive.N2C
