import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.transportCurves
import Submission.Work.Drive.N2.bandLaw

/-!
# `N2C` A2: transporting a level parametrisation along the level flow

`Work.Drive.N2C.LevelCurves f b n` records the parametrisation rows of the level `f = b` by `n`
periodic curves.  Given a flow `Φ` which advances `f` at unit speed on the value band `(a,c)`
(`hΦf`), the transport

  `γ' i t = Φ (b' - b, γ i t)`

parametrises the level `f = b'` with all the same rows.  This is A2 of the coherent-window
architecture: the labels (the curves `γ i`) may be *reused* across a critical-free band.

`Work.Drive.N2.transportCurves` already supplies the rows `sm`, `val`, `per`, `modOne`, `cover`,
`disj`.  What is added here is

* `injIco`, which follows from `modOne` (two parameters in `[0,1)` of the same curve differ by an
  integer, hence by `0`);
* `ker`: the derivative of the transported curve spans the kernel of `mfderiv f` at the transported
  point.  The flow map at a fixed time is a diffeomorphism of `M` (its inverse is the flow map at
  the opposite time) which shifts the values of `f` by a constant near a level, hence intertwines
  the kernels of `mfderiv f`; the chain rule then transports the `ker` row of `L`.

The only analytic input is the fact that `mfderiv` is unchanged by adding a constant to a real
valued function (`mfderiv_add_const` / `mfderiv_sub_const` below).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- **The derivative of a real-valued function is unchanged by adding a constant to its values.** -/
theorem mfderiv_add_const {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → ℝ} {c : ℝ} {y : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f y) :
    mfderiv I 𝓘(ℝ, ℝ) (fun z => f z + c) y = mfderiv I 𝓘(ℝ, ℝ) f y := by
  have hg : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun t : ℝ => t + c) (f y) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact differentiableAt_id.add_const c
  have hshift : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun t : ℝ => t + c) (f y)
      = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv, show (fun t : ℝ => t + c) = (fun t : ℝ => id t + c) from rfl,
      fderiv_add_const, fderiv_id]
  have key : (fun z : M => f z + c) = (fun t : ℝ => t + c) ∘ f := rfl
  ext v
  rw [key, mfderiv_comp_apply (I := I) y hg hf v, hshift]
  rfl

/-- **The derivative of a real-valued function is unchanged by subtracting a constant from its
values.** -/
theorem mfderiv_sub_const {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {f : M → ℝ} {c : ℝ} {y : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f y) :
    mfderiv I 𝓘(ℝ, ℝ) (fun z => f z - c) y = mfderiv I 𝓘(ℝ, ℝ) f y := by
  have hg : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun t : ℝ => t - c) (f y) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact differentiableAt_id.sub_const c
  have hshift : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun t : ℝ => t - c) (f y)
      = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv, show (fun t : ℝ => t - c) = (fun t : ℝ => id t - c) from rfl,
      fderiv_sub_const, fderiv_id]
  have key : (fun z : M => f z - c) = (fun t : ℝ => t - c) ∘ f := rfl
  ext v
  rw [key, mfderiv_comp_apply (I := I) y hg hf v, hshift]
  rfl

theorem levelCurves_transport {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f)
    {a c b b' : ℝ} (hab : a < b) (hbc : b < c) (hab' : a < b') (hb'c : b' < c)
    {Φ : ℝ × M → M}
    (hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a c → f x + t ∈ Set.Icc a c →
      f (Φ (t, x)) = f x + t)
    {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) :
    Nonempty (Work.Drive.N2C.LevelCurves f b' n) := by
  obtain ⟨γ, hsm, hval, hper, hinj, hmod, hcov, hdisj, hker⟩ := L
  have hcont : Continuous f := hf.continuous
  have hfmd : ∀ y : M, MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℝ) f y := fun y => hf.mdifferentiableAt (by simp)
  -- The flow map at time `b' - b` is inverted by the flow map at time `b - b'`.
  have htr : ∀ y : M, Φ (b' - b, Φ (b - b', y)) = y := fun y => by
    rw [hΦcomp, show (b' - b) + (b - b') = 0 by ring, hΦ0]
  have hrt : ∀ y : M, Φ (b - b', Φ (b' - b, y)) = y := fun y => by
    rw [hΦcomp, show (b - b') + (b' - b) = 0 by ring, hΦ0]
  let γ' : Fin n → ℝ → M := fun i t => Φ (b' - b, γ i t)
  -- the level value
  have hval' : ∀ (i : Fin n) (x : ℝ), f (γ' i x) = b' := by
    intro i x
    have h := hΦf (γ i x) (b' - b) (by rw [hval i x]; exact ⟨hab.le, hbc.le⟩)
      (by rw [hval i x]; constructor <;> linarith)
    rw [hval i x] at h
    rw [show b + (b' - b) = b' by ring] at h
    exact h
  -- smoothness
  have hsm' : ∀ i : Fin n, ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ((⊤:ℕ∞):WithTop ℕ∞) (γ' i) := by
    intro i
    exact hΦsm.comp (contMDiff_const.prodMk (hsm i))
  -- periodicity
  have hper' : ∀ (i : Fin n) (x : ℝ), γ' i (x + 1) = γ' i x := by
    intro i x
    show Φ (b' - b, γ i (x + 1)) = Φ (b' - b, γ i x)
    rw [hper i x]
  -- the "mod 1" row: the flow is injective, so it is inherited from `L`
  have hmod' : ∀ (i : Fin n) (x y : ℝ), γ' i x = γ' i y → ∃ k : ℤ, x = y + k := by
    intro i x y hxy
    have h2 : Φ (b - b', Φ (b' - b, γ i x)) = Φ (b - b', Φ (b' - b, γ i y)) :=
      congrArg (fun z : M => Φ (b - b', z)) hxy
    rw [hrt (γ i x), hrt (γ i y)] at h2
    exact hmod i x y h2
  -- injectivity on `[0,1)`, from the "mod 1" row
  have hinjIco' : ∀ i : Fin n, Set.InjOn (γ' i) (Set.Ico 0 1) := by
    intro i x hx y hy hxy
    obtain ⟨k, hk⟩ := hmod' i x y hxy
    have hx' : (0:ℝ) ≤ x ∧ x < 1 := by simpa [Set.mem_Ico] using hx
    have hy' : (0:ℝ) ≤ y ∧ y < 1 := by simpa [Set.mem_Ico] using hy
    have hk1 : (k:ℝ) < 1 := by linarith
    have hk2 : (-1:ℝ) < (k:ℝ) := by linarith
    have hklt : k < 1 := by exact_mod_cast hk1
    have hkgt : -1 < k := by exact_mod_cast hk2
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    simpa using hk
  -- the covering row
  have hcov' : ∀ x : M, f x = b' → ∃ (i : Fin n) (t : ℝ), x = γ' i t := by
    intro x hx
    have h1 : f (Φ (b - b', x)) = b := by
      have h := hΦf x (b - b') (by rw [hx]; exact ⟨hab'.le, hb'c.le⟩)
        (by rw [hx]; constructor <;> linarith)
      rw [hx] at h
      rw [show b' + (b - b') = b by ring] at h
      exact h
    obtain ⟨i, t, ht⟩ := hcov (Φ (b - b', x)) h1
    refine ⟨i, t, ?_⟩
    show x = Φ (b' - b, γ i t)
    rw [← ht]
    exact (htr x).symm
  -- disjointness of the ranges
  have hdisj' : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ' i)) (Set.range (γ' j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro z ⟨s, rfl⟩ ⟨u, hu⟩
    have h1 : γ j u = γ i s := by
      have h2 : Φ (b - b', Φ (b' - b, γ j u)) = Φ (b - b', Φ (b' - b, γ i s)) :=
        congrArg (fun z : M => Φ (b - b', z)) hu
      rw [hrt (γ j u), hrt (γ i s)] at h2
      exact h2
    exact Set.disjoint_left.mp (hdisj i j hij) ⟨s, rfl⟩ ⟨u, h1⟩
  -- the `ker` row: transport of the kernel of `mfderiv f` by the flow
  have hker' : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ' i x)),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ' i x) v = 0 →
      ∃ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' i) x t = v := by
    intro i x v hv
    let T : M → M := fun y => Φ (b' - b, y)
    let R : M → M := fun y => Φ (b - b', y)
    have hTsm : ContMDiff (𝓡 2) (𝓡 2) ((⊤:ℕ∞):WithTop ℕ∞) T :=
      hΦsm.comp (contMDiff_const.prodMk contMDiff_id)
    have hRsm : ContMDiff (𝓡 2) (𝓡 2) ((⊤:ℕ∞):WithTop ℕ∞) R :=
      hΦsm.comp (contMDiff_const.prodMk contMDiff_id)
    have hTmd : ∀ y : M, MDifferentiableAt (𝓡 2) (𝓡 2) T y :=
      fun y => hTsm.mdifferentiableAt (by simp)
    have hRmd : ∀ y : M, MDifferentiableAt (𝓡 2) (𝓡 2) R y :=
      fun y => hRsm.mdifferentiableAt (by simp)
    have hRz : R (γ' i x) = γ i x := by
      show Φ (b - b', Φ (b' - b, γ i x)) = γ i x
      exact hrt (γ i x)
    -- `f ∘ R = f - (b' - b)` on a neighbourhood of `γ' i x`
    have hbandR : (fun y : M => f (R y)) =ᶠ[𝓝 (γ' i x)] (fun y : M => f y - (b' - b)) := by
      have hzval : f (γ' i x) = b' := hval' i x
      have hmem1 : f (γ' i x) ∈ Set.Ioo a c :=
        ⟨by rw [hzval]; exact hab', by rw [hzval]; exact hb'c⟩
      have hmem2 : f (γ' i x) - (b' - b) ∈ Set.Ioo a c := by
        have he : f (γ' i x) - (b' - b) = b := by rw [hzval]; ring
        rw [he]; exact ⟨hab, hbc⟩
      have hopen1 : IsOpen {y : M | f y ∈ Set.Ioo a c} := isOpen_Ioo.preimage hcont
      have hopen2 : IsOpen {y : M | f y - (b' - b) ∈ Set.Ioo a c} :=
        isOpen_Ioo.preimage (hcont.sub continuous_const)
      filter_upwards [hopen1.mem_nhds hmem1, hopen2.mem_nhds hmem2] with y hy1 hy2
      have hb : f y + (b - b') ∈ Set.Icc a c := by
        have he : f y + (b - b') = f y - (b' - b) := by ring
        rw [he]; exact ⟨le_of_lt hy2.1, le_of_lt hy2.2⟩
      have h := hΦf y (b - b') ⟨le_of_lt hy1.1, le_of_lt hy1.2⟩ hb
      show f (Φ (b - b', y)) = f y - (b' - b)
      rw [h]
      ring
    have hfR : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (fun y : M => f (R y)) (γ' i x)
        = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ' i x) := by
      rw [Filter.EventuallyEq.mfderiv_eq hbandR]
      exact mfderiv_sub_const (f := f) (c := b' - b) (y := γ' i x) (hfmd (γ' i x))
    -- the vector `w := dR v` again lies in the kernel of `mfderiv f` (at the point of `L`)
    have hw0 : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i x) (mfderiv (𝓡 2) (𝓡 2) R (γ' i x) v) = 0 := by
      have h1 : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (fun y : M => f (R y)) (γ' i x) v
          = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i x) ((mfderiv (𝓡 2) (𝓡 2) R (γ' i x)) v) :=
        mfderiv_comp_apply_of_eq (x := γ' i x) (g := f) (f := R) (y := γ i x)
          (hfmd (γ i x)) (hRmd (γ' i x)) hRz v
      rw [hfR] at h1
      rw [← h1]
      exact hv
    obtain ⟨t, ht⟩ := hker i x (mfderiv (𝓡 2) (𝓡 2) R (γ' i x) v) hw0
    refine ⟨t, ?_⟩
    -- the chain rule for `γ' i = T ∘ γ i`
    have h2 : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ' i) x t
        = mfderiv (𝓡 2) (𝓡 2) T (γ i x) ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) x) t) := by
      have heq : (γ' i) = T ∘ γ i := rfl
      rw [heq]
      exact mfderiv_comp_apply (x := x) (g := T) (f := γ i) (hTmd (γ i x))
        ((hsm i).mdifferentiableAt (by simp)) t
    rw [h2, ht]
    -- `T` and `R` are mutually inverse, so `dT (dR v) = v`
    have h3 : mfderiv (𝓡 2) (𝓡 2) (T ∘ R) (γ' i x) v = v := by
      have heq : (T ∘ R) = id := funext (fun y => htr y)
      rw [heq, mfderiv_id]
      rfl
    have h4 : mfderiv (𝓡 2) (𝓡 2) (T ∘ R) (γ' i x) v
        = mfderiv (𝓡 2) (𝓡 2) T (γ i x) ((mfderiv (𝓡 2) (𝓡 2) R (γ' i x)) v) :=
      mfderiv_comp_apply_of_eq (x := γ' i x) (g := T) (f := R) (y := γ i x)
        (hTmd (γ i x)) (hRmd (γ' i x)) hRz v
    rw [h4] at h3
    exact h3
  exact ⟨{ γ := γ', sm := hsm', val := hval', per := hper', injIco := hinjIco',
           modOne := hmod', cover := hcov', disj := hdisj', ker := hker' }⟩

end Work.Drive.N2C
