import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.GoodDrawingFamily

/-!
# Negation transfer (`f ↦ -f`) — the Möbius/merge case of the `D2` assembly

The saddle window `D2` (`Work.N2C.exists_certifiedWindow_saddle`) is proved in two cases, and the
"merge" case is *not* given a picture directly: a merged saddle for `f` is a split saddle for `-f`
(`N2Lead/NOTES_LEAD_saddlePacket.md` §0.4 — the anchor-hyperbola remnants of a merge are traversed
backwards about every centre, so no star-shaped picture of the merged level exists).  The transfer
`f ↦ -f` therefore has to be formalised once and for all.  This file provides it:

* `isCritical_neg_iff`, `nondegHess_neg`, `nondegCrit_neg_iff`, `IsMorseDistinct.neg`;
* `Work.Drive.N2C.WindowDatum.neg` — the window datum of `-f` at the same point, with the *reversed*
  flow `Φ' (t, y) = Φ (-t, y)` and the signs `s₁, s₂` flipped;
* `goodDrawingOn_neg_iff` — a good drawing for `f` on the band `A` is a good drawing for `-f` on the
  band `-A` (the *same* map `g`);
* `levelCurves_neg_iff`, `isLevelIsotopy_neg_iff`, `isCertifiedAt_neg_iff` — the certificate is
  invariant under `f ↦ -f` with `u ↦ -u`, because the level set, its tangent space and the round
  configurations are unchanged.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The Morse-theoretic vocabulary under `f ↦ -f` -/

theorem isCritical_neg_iff (f : M → ℝ) (x : M) :
    Work.Drive.Morse.IsCritical (fun y : M => -f y) x ↔ Work.Drive.Morse.IsCritical f x := by
  have hfun : (fun y : M => -f y) = -f := rfl
  rw [Work.Drive.Morse.IsCritical, Work.Drive.Morse.IsCritical, hfun, mfderiv_neg]
  exact neg_eq_zero

/-- The vanishing of the differential is unchanged under `f ↦ -f` (the two values live in the
tangent spaces of `-f x` and of `f x`, which are the same model space; the equation is proved at the
`ContinuousLinearMap` level to avoid the `TangentSpace` instance mismatch). -/
theorem mfderiv_neg_apply_eq_zero_iff (f : M → ℝ) (x : M) (v : TangentSpace (𝓡 2) x) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : M => -f y) x v = 0 ↔
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 := by
  have hCLM : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : M => -f y) x
      = -mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x := by
    rw [show (fun y : M => -f y) = -f from rfl, mfderiv_neg]
  have h : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : M => -f y) x v
      = -mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v := congrArg (fun T => T v) hCLM
  rw [h]
  exact neg_eq_zero

/-- The Hessian of the negation of a function is the negation of the Hessian. -/
theorem nondegHess_neg (F : EuclideanSpace ℝ (Fin 2) → ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ (fun z => -F z)) y = -fderiv ℝ (fderiv ℝ F) y := by
  have h1 : (fun z : EuclideanSpace ℝ (Fin 2) => -F z) = -F := rfl
  have h2 : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => -F z)
      = fun z => -(fderiv ℝ F z) := by
    rw [h1]
    funext z
    rw [fderiv_neg]
  rw [h2]
  have h3 : (fun z : EuclideanSpace ℝ (Fin 2) => -(fderiv ℝ F z)) = -(fderiv ℝ F) := rfl
  rw [h3, fderiv_neg]

theorem nondegCrit_neg_iff (f : M → ℝ) (x : M) :
    Work.Drive.Morse.NondegCrit (fun y : M => -f y) x ↔ Work.Drive.Morse.NondegCrit f x := by
  have hchart : (fun y : M => -f y) ∘ (extChartAt (𝓡 2) x).symm
      = fun z => -((f ∘ (extChartAt (𝓡 2) x).symm) z) := rfl
  have hnew : fderiv ℝ (fderiv ℝ ((fun y : M => -f y) ∘ (extChartAt (𝓡 2) x).symm))
        (extChartAt (𝓡 2) x x)
      = -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 2) x).symm)) (extChartAt (𝓡 2) x x) := by
    rw [hchart]
    exact nondegHess_neg (f ∘ (extChartAt (𝓡 2) x).symm) (extChartAt (𝓡 2) x x)
  rw [Work.Drive.Morse.NondegCrit, Work.Drive.Morse.NondegCrit, isCritical_neg_iff, hnew]
  constructor
  · rintro ⟨hc, hi⟩
    exact ⟨hc, fun a b hab => hi (congrArg Neg.neg hab)⟩
  · rintro ⟨hc, hi⟩
    exact ⟨hc, fun a b hab => hi (neg_injective hab)⟩

theorem IsMorseDistinct.neg {f : M → ℝ} (hf : Work.Drive.Morse.IsMorseDistinct f) :
    Work.Drive.Morse.IsMorseDistinct (fun x : M => -f x) := by
  refine ⟨hf.1.neg, ?_, ?_⟩
  · intro x hx
    exact (nondegCrit_neg_iff f x).mpr (hf.2.1 x ((isCritical_neg_iff f x).mp hx))
  · intro x y hx hy hxy
    refine hf.2.2 x y ((isCritical_neg_iff f x).mp hx) ((isCritical_neg_iff f y).mp hy) ?_
    linarith

/-! ## The window datum of `-f` -/

/-- The reindexing of the interval `Icc (min 0 t) (max 0 t)` under `t ↦ -t`. -/
theorem mem_Icc_min_max_neg (t u : ℝ) :
    u ∈ Set.Icc (min 0 t) (max 0 t) ↔ -u ∈ Set.Icc (min 0 (-t)) (max 0 (-t)) := by
  rcases le_total 0 t with ht | ht
  · rw [min_eq_left ht, max_eq_right ht, min_eq_right (by linarith : -t ≤ 0),
      max_eq_left (by linarith : -t ≤ 0)]
    simp only [Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith
  · rw [min_eq_right ht, max_eq_left ht, min_eq_left (by linarith : (0:ℝ) ≤ -t),
      max_eq_right (by linarith : (0:ℝ) ≤ -t)]
    simp only [Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith

theorem chartQ_neg (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ℝ) (y : M) :
    Work.Drive.N2.chartQ φ (-s₁) (-s₂) y = -Work.Drive.N2.chartQ φ s₁ s₂ y := by
  rw [Work.Drive.N2.chartQ, Work.Drive.N2.chartQ]
  ring

/-- **The window datum of `-f`.**  Same charts, same model balls, same critical enumeration, but the
signs `s₁, s₂` are flipped, `ηd` is unchanged and the flow is the *reversed* one
`Φ' (t, y) = Φ (-t, y)`.  Every row is a short computation; the only one that is not completely
formal is `hmono`, which uses that `hmono` of the datum gives monotonicity in *all* times (the group
law turns the one-sided hypothesis at `Φ (a, y)` into the two-sided statement at `y`). -/
noncomputable def WindowDatum.neg {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) :
    Work.Drive.N2.WindowDatum (fun x : M => -f x) p where
  N := D.N
  x := D.x
  φ := D.φ
  s₁ := fun i => -D.s₁ i
  s₂ := fun i => -D.s₂ i
  ρ := D.ρ
  C := D.C
  j := D.j
  hxj := D.hxj
  hinj := D.hinj
  hcrit := fun i => (isCritical_neg_iff f (D.x i)).mpr (D.hcrit i)
  hcover := fun y hy => by
    obtain ⟨i, hi⟩ := D.hcover y ((isCritical_neg_iff f y).mp hy)
    exact ⟨i, hi⟩
  hρ := D.hρ
  hsrc := D.hsrc
  hcen := D.hcen
  hsgn := fun i => by
    obtain ⟨h₁, h₂⟩ := D.hsgn i
    have aux : ∀ s : ℝ, (s = 1 ∨ s = -1) → (-s = 1 ∨ -s = -1) := by
      rintro s (rfl | rfl) <;> simp
    exact ⟨aux _ h₁, aux _ h₂⟩
  hval := fun i y hy => by
    rw [D.hval i y hy, chartQ_neg]
    ring
  hφ := D.hφ
  hφ' := D.hφ'
  hdisj := D.hdisj
  hCsub := D.hCsub
  hCclosed := D.hCclosed
  hCcl := D.hCcl
  hCball := D.hCball
  hCop := D.hCop
  ηd := D.ηd
  hηd := D.hηd
  hηd' := D.hηd'
  hsep := fun i j' hij => by
    have h : |-f (D.x i) - -f (D.x j')| = |f (D.x i) - f (D.x j')| := by
      rw [show -f (D.x i) - -f (D.x j') = -(f (D.x i) - f (D.x j')) by ring, abs_neg]
    rw [h]
    exact D.hsep i j' hij
  hsepK := fun i j' hij z hz => by
    have h : |-f z - -f (D.x j')| = |f z - f (D.x j')| := by
      rw [show -f z - -f (D.x j') = -(f z - f (D.x j')) by ring, abs_neg]
    rw [h]
    exact D.hsepK i j' hij z hz
  Φ := fun q => D.Φ (-q.1, q.2)
  hΦsm := by
    have h1 : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (𝓡 2))
        ((modelWithCornersSelf ℝ ℝ).prod (𝓡 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × M => ((-q.1, q.2) : ℝ × M)) :=
      ContMDiff.prodMk contMDiff_fst.neg contMDiff_snd
    exact D.hΦsm.comp h1
  hΦ0 := fun y => by
    show D.Φ (-(0 : ℝ), y) = y
    rw [neg_zero, D.hΦ0]
  hΦcomp := fun a b y => by
    show D.Φ (-a, D.Φ (-b, y)) = D.Φ (-(a + b), y)
    rw [D.hΦcomp]
    ring_nf
  hlevel := fun y t hconf => by
    show -f (D.Φ (-t, y)) = -f y + t
    have hconf' : ∀ u ∈ Set.Icc (min 0 (-t)) (max 0 (-t)), ∀ i,
        D.Φ (u, y) ∉ Work.Drive.N2.modelBall (D.φ i) (D.ρ i / 8) := by
      intro u hu i
      have h1 : -u ∈ Set.Icc (min 0 t) (max 0 t) := by
        rw [mem_Icc_min_max_neg t (-u)]
        simpa using hu
      have h2 := hconf (-u) h1 i
      simpa using h2
    have h := D.hlevel y (-t) hconf'
    linarith
  hODE := fun i y t hconf => by
    have hconf' : ∀ u ∈ Set.Icc (min 0 (-t)) (max 0 (-t)), D.Φ (u, y) ∈ D.C i := by
      intro u hu
      have h1 : -u ∈ Set.Icc (min 0 t) (max 0 t) := by
        rw [mem_Icc_min_max_neg t (-u)]
        simpa using hu
      have h2 := hconf (-u) h1
      simpa using h2
    obtain ⟨h0, h1⟩ := D.hODE i y (-t) hconf'
    have hc : HasDerivAt (fun σ : ℝ => -σ) (-1) t := hasDerivAt_neg t
    constructor
    · have hcomp' : HasDerivAt (fun σ : ℝ => D.φ i (D.Φ (-σ, y)) 0)
          ((Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * (D.s₁ i * D.φ i (D.Φ (-t, y)) 0)) * (-1)) t := by
        simpa only [Function.comp_def] using h0.comp t hc
      rw [show (Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * (D.s₁ i * D.φ i (D.Φ (-t, y)) 0)) * (-1)
          = Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * ((-D.s₁ i) * D.φ i (D.Φ (-t, y)) 0) from by ring] at hcomp'
      exact hcomp'
    · have hcomp' : HasDerivAt (fun σ : ℝ => D.φ i (D.Φ (-σ, y)) 1)
          ((Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * (D.s₂ i * D.φ i (D.Φ (-t, y)) 1)) * (-1)) t := by
        simpa only [Function.comp_def] using h1.comp t hc
      rw [show (Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * (D.s₂ i * D.φ i (D.Φ (-t, y)) 1)) * (-1)
          = Work.Drive.N2.chartMult (D.ρ i / 8) (‖D.φ i (D.Φ (-t, y))‖ ^ 2)
            * ((-D.s₂ i) * D.φ i (D.Φ (-t, y)) 1) from by ring] at hcomp'
      exact hcomp'
  hmono := fun y => by
    have hglob : Monotone fun t : ℝ => f (D.Φ (t, y)) := by
      intro a b hab
      have h1 : (0 : ℝ) ≤ b - a := by linarith
      have hzero : (0 : ℝ) ∈ Set.Ici 0 := by simp
      have h : f (D.Φ (0, D.Φ (a, y))) ≤ f (D.Φ (b - a, D.Φ (a, y))) :=
        D.hmono (D.Φ (a, y)) hzero h1 (by linarith)
      rw [D.hΦ0 (D.Φ (a, y)), D.hΦcomp (b - a) a y] at h
      have harg : b - a + a = b := by ring
      rw [harg] at h
      exact h
    intro a ha b hb hab
    show -f (D.Φ (-a, y)) ≤ -f (D.Φ (-b, y))
    have h := hglob (show -b ≤ -a by linarith)
    linarith

/-! ## Good drawings and certificates under `f ↦ -f` -/

/-- A good drawing for `f` on the band `A` is a good drawing for `-f` on the band `-A`, with the
same picture. -/
theorem goodDrawingOn_neg_iff {f : M → ℝ} {A : Set ℝ} {g : M → EuclideanSpace ℝ (Fin 3)} :
    Work.Drive.N2.GoodDrawingOn f A g ↔
      Work.Drive.N2.GoodDrawingOn (fun x : M => -f x) {t : ℝ | -t ∈ A} g := by
  have hfun : (fun y : M => -f y) = -f := rfl
  have hderiv : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : M => -f y) x v = 0 ↔
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 :=
    fun x v => mfderiv_neg_apply_eq_zero_iff f x v
  constructor
  · rintro ⟨hsm, himm, hinj⟩
    refine ⟨fun x hx => hsm x (by simpa using hx),
      fun x hx v hv hv' => himm x (by simpa using hx) v ((hderiv x v).mp hv) hv', ?_⟩
    intro x y hx hy hfxy hg
    exact hinj x y (by simpa using hx) (by simpa using hy) (by linarith) hg
  · rintro ⟨hsm, himm, hinj⟩
    refine ⟨fun x hx => hsm x (by simpa using hx),
      fun x hx v hv hv' => himm x (by simpa using hx) v ((hderiv x v).mpr hv) hv', ?_⟩
    intro x y hx hy hfxy hg
    exact hinj x y (by simpa using hx) (by simpa using hy) (by linarith) hg

/-- The level-curve rows are unchanged under `f ↦ -f`, `u ↦ -u`. -/
def LevelCurves.neg {f : M → ℝ} {u : ℝ} {n : ℕ} (L : LevelCurves f u n) :
    LevelCurves (fun x : M => -f x) (-u) n where
  γ := L.γ
  sm := L.sm
  val := fun i x => by have h := L.val i x; linarith
  per := L.per
  injIco := L.injIco
  modOne := L.modOne
  cover := fun x hx => L.cover x (by linarith)
  disj := L.disj
  ker := fun i x v hv => L.ker i x v ((mfderiv_neg_apply_eq_zero_iff f (L.γ i x) v).mp hv)

/-- The inverse direction of `LevelCurves.neg`. -/
def LevelCurves.negInv {f : M → ℝ} {u : ℝ} {n : ℕ}
    (L : LevelCurves (fun x : M => -f x) (-u) n) : LevelCurves f u n where
  γ := L.γ
  sm := L.sm
  val := fun i x => by have h := L.val i x; linarith
  per := L.per
  injIco := L.injIco
  modOne := L.modOne
  cover := fun x hx => L.cover x (by linarith)
  disj := L.disj
  ker := fun i x v hv => L.ker i x v ((mfderiv_neg_apply_eq_zero_iff f (L.γ i x) v).mpr hv)

/-- The level-isotopy row is unchanged under `f ↦ -f`, `u ↦ -u`. -/
theorem isLevelIsotopy_neg_iff {f : M → ℝ} {u : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)} :
    IsLevelIsotopy f u e ↔ IsLevelIsotopy (fun x : M => -f x) (-u) e := by
  have hfun : (fun x : M => -f x) = -f := rfl
  have hderiv : ∀ y : M, ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun x : M => -f x) y v = 0 ↔
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 :=
    fun y v => mfderiv_neg_apply_eq_zero_iff f y v
  constructor
  · rintro ⟨hsm, hinj, himm⟩
    refine ⟨fun s y hy => hsm s y (by simpa using hy),
      fun s x y hx hy h => hinj s x y (by simpa using hx) (by simpa using hy) h,
      fun s y hy v hv hv' => himm s y (by simpa using hy) v ((hderiv y v).mp hv) hv'⟩
  · rintro ⟨hsm, hinj, himm⟩
    refine ⟨fun s y hy => hsm s y (by simpa using hy),
      fun s x y hx hy h => hinj s x y (by simpa using hx) (by simpa using hy) h,
      fun s y hy v hv hv' => himm s y (by simpa using hy) v ((hderiv y v).mpr hv) hv'⟩

/-- The certificate is unchanged under `f ↦ -f`, `u ↦ -u`. -/
theorem isCertifiedAt_neg_iff {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {u : ℝ} {g : M → EuclideanSpace ℝ (Fin 3)} :
    IsCertifiedAt f u g ↔ IsCertifiedAt (fun x : M => -f x) (-u) g := by
  constructor
  · rintro ⟨n, L, D, e, hD, hiso, h0, h1⟩
    exact ⟨n, L.neg, D, e, hD, (isLevelIsotopy_neg_iff).mp hiso,
      fun y hy => h0 y (by linarith), h1⟩
  · rintro ⟨n, L, D, e, hD, hiso, h0, h1⟩
    exact ⟨n, L.negInv, D, e, hD, (isLevelIsotopy_neg_iff).mpr hiso,
      fun y hy => h0 y (by linarith), h1⟩

end Work.Drive.N2C
