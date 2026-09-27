import Mathlib
import Submission.Work.Drive.PushDisc.flatTubeStraightSpine
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Drive.PushDisc.sheetChartOfFlatTube
import Submission.Work.Drive.PushDisc.exists_straightFlatTube
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology
open Set

/-!
# A smooth chart of `M` adapted to the second bigon arc `γ₂`

The main result is `exists_chart_of_arc`, the exact `p₁ ↔ p₂`, `q₁ ↔ q₂` mirror of the chain
`flatTubeStraightSpine` + `straightFlatTubeOfFlatTube`.

The three ingredients proved in this file are
* `cast_smul_fin` / `cast_splitE_smul` / `cast_splitE_one_ne_zero`: the bookkeeping of the type equality
  `ℝ^{k+1} = ℝⁿ` (`Fin (k+1) → ℝ` vs `Fin n → ℝ`) for the non-zero vector `splitE k (1,0)`;
* `exists_linearEquiv_map_eq_ne_zero`: a linear equivalence of finite-dimensional spaces of equal
  dimension carrying one nonzero vector to another one (used to straighten the arc's chord on the
  `splitE k (1,0)`-axis);
* the assembly below: the flat tube around `γ₂` is turned into a chart by the inverse function
  theorem (`exists_smoothChart_of_injOn_immersion_of_nonempty_source`), the affine normalisation of
  the arc being folded into the chart map `G`.
-/

/-- `Eq.rec` along `k + 1 = n` commutes with scalar multiplication.  (§ of the transport bookkeeping:
the cast is the identity on the `Fin`-indexed Euclidean spaces, so `cases` closes it.) -/
theorem cast_smul_fin {k n : ℕ} (hk : k + 1 = n) (a : ℝ) (y : EuclideanSpace ℝ (Fin (k + 1))) :
    hk ▸ (a • y) = a • (hk ▸ y) := by
  cases hk
  rfl

/-- The cast of the straight segment vector `splitE k (a, 0)` is `a` times the cast of the unit
vector `splitE k (1, 0)`. -/
theorem cast_splitE_smul {k n : ℕ} (hk : k + 1 = n) (a : ℝ) :
    hk ▸ (splitE k ((a, (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k)))
      = a • (hk ▸ (splitE k (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :
          ℝ × EuclideanSpace ℝ (Fin k)))) := by
  have h : (splitE k ((a, (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k)))
      = a • (splitE k (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :
          ℝ × EuclideanSpace ℝ (Fin k))) := by
    rw [show ((a, (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k))
        = a • (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k)) from by
      ext <;> simp]
    exact map_smul _ _ _
  exact (congrArg (fun x => hk ▸ x) h).trans (cast_smul_fin hk a _)

/-- The transported unit vector of `splitE` is nonzero. -/
theorem cast_splitE_one_ne_zero {k n : ℕ} (hk : k + 1 = n) :
    (hk ▸ (splitE k (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :
      ℝ × EuclideanSpace ℝ (Fin k)))) ≠ 0 := by
  cases hk
  intro h
  refine (show (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k)) ≠ 0
    by simp) ?_
  exact (splitE k).injective (h.trans (map_zero (splitE k)).symm)

/-- **A linear equivalence of finite-dimensional spaces of equal dimension carrying one nonzero
vector to another one.**  The proof decomposes both spaces along the lines spanned by the two
vectors and glues a pinned isomorphism of the lines with an arbitrary isomorphism of complements. -/
theorem exists_linearEquiv_map_eq_ne_zero {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (h : Module.finrank ℝ V = Module.finrank ℝ W) {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : V ≃ₗ[ℝ] W, e v = w := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span ℝ ({v} : Set V))
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (Submodule.span ℝ ({w} : Set W))
  obtain ⟨e₀, he₀⟩ := Work.Drive.Whitney.span_equiv_span_of_ne_zero hv hw
  have hdim : Module.finrank ℝ C = Module.finrank ℝ C' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := Submodule.finrank_add_eq_of_isCompl hC'
    rw [finrank_span_singleton hv] at h1
    rw [finrank_span_singleton hw] at h2
    omega
  refine ⟨(Submodule.prodEquivOfIsCompl (Submodule.span ℝ ({v} : Set V)) C hC).symm.trans
    ((e₀.prodCongr (LinearEquiv.ofFinrankEq C C' hdim)).trans
      (Submodule.prodEquivOfIsCompl (Submodule.span ℝ ({w} : Set W)) C' hC')), ?_⟩
  show (Submodule.prodEquivOfIsCompl (Submodule.span ℝ ({w} : Set W)) C' hC')
      ((e₀.prodCongr (LinearEquiv.ofFinrankEq C C' hdim))
        ((Submodule.prodEquivOfIsCompl (Submodule.span ℝ ({v} : Set V)) C hC).symm
          ((⟨v, Submodule.mem_span_singleton_self v⟩ : ↥(Submodule.span ℝ ({v} : Set V))) : V))) = w
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  rw [LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl']
  rw [he₀]
  simp

/-- **A smooth chart of `M` adapted to the second bigon arc `γ₂`.**  This is the exact
`p₁ ↔ p₂`, `q₁ ↔ q₂` mirror of the already-proved chain
`Work.Drive.PushDisc.flatTubeStraightSpine` (which is stated for the arc from `p₁` to `q₁`, excluding
the points `p₂, q₂`) followed by `Work.Drive.PushDisc.straightFlatTubeOfFlatTube` /
`Work.Whitney.exists_smoothChart_of_injOn_immersion_of_nonempty`.

Route (reviewer-verified, both reviewers: "looks correct as stated"):
* instantiate `flatTubeStraightSpine` with `(p₁,p₂,q₁,q₂) := (p₂,p₁,q₂,q₁)` and `γ₁ := γ₂`
  (its `hclean'` has exactly the disjunct order written here; `hp₁arc`/`hq₁arc` are the two
  "points off the arc" that `Work.Whitney.CutPush.exists_tube_injOn` consumes).  This gives a global
  diffeo `A` of `ℝ^{2n}`, an `n`-plane `K`, and an open tube `U ∋ γ₂ '' Icc` with `closure U ⊆ W`,
  `p₁, q₁ ∉ U`, `A (f x) ∈ K` for `x ∈ U`, and the *arc row*
  `A (f (γ₂ t)) = A (f p₂) + t • (A (f q₂) - A (f p₂))`;
* the map `g : M → K ≅ E^{k+1}`, `g x := A (f x)` (composed with a linear iso `K ≅ ℝ^{k+1}`) is
  a smooth immersion with injective `mfderiv` on `U` (its derivative lands in `K`, of dimension
  `n = k+1`) and injective on `U` (by `hclean`: `p₁, q₁ ∉ U` excludes all four double pairs), so
  `Work.Whitney.exists_smoothChart_of_injOn_immersion_of_nonempty_source` (or the
  `_of_nonempty` variant) produces an `OpenPartialHomeomorph` `c` with `c.source = U` and `c = g`
  on `U`, which is `IsSmoothChart`;
* `c (γ₂ t) = g (γ₂ t) = (the linear iso) (A (f p₂) + t • (A (f q₂) - A (f p₂)))`; post-composing
  the chart with the *affine* isomorphism of `E^n` sending `g (γ₂ 0) ↦ splitE k ((-1,0))` and
  `g (γ₂ 1) ↦ splitE k ((1,0))` (distinct because `hclean` + `hγ₂inj` + `hp₁arc`/`hq₁arc` give
  `f p₂ ≠ f q₂`; affine maps are smooth with smooth inverse, so `IsSmoothChart` survives) gives the
  claimed row. -/
theorem exists_chart_of_arc {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₂ : p₂ ∈ W) (hW₄ : q₂ ∈ W) (hp₂p₁ : p₂ ≠ p₁)
    (hfp : f p₂ = f p₁)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₂ ∧ z = p₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = q₂ ∧ z = q₁) ∨
        (y = q₁ ∧ z = q₂))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hp₁arc : p₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1) (hq₁arc : q₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (hk : k + 1 = n)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      Work.Whitney.IsSmoothChart c ∧ c.source ⊆ W ∧
      γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ c.source ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        c (γ₂ t) = hk ▸ (Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), 0))) := by
  classical
  -- ## the flat tube around `γ₂` (the mirror of the first arc's tube)
  obtain ⟨A, Ainv, K, U, hA, hAinv, hAl, hAr, hKfin, hUo, hUclW, hUarc, hp₁U, hq₁U, hflat, hrow⟩ :=
    flatTubeStraightSpine hn f hf himm W hWopen hWcpt p₂ p₁ q₂ q₁ hW₂ hW₄
      hp₂p₁ hfp hclean hsep γ₂ hγ₂ hγ₂0 hγ₂1 hγW₂ hγ₂inj hγ₂smooth hγ₂imm hp₁arc hq₁arc
  have hUW : U ⊆ W := Subset.trans subset_closure hUclW
  have hp₂U : p₂ ∈ U := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₂0⟩
  have hq₂U : q₂ ∈ U := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₂1⟩
  -- ## the two endpoints of the arc have different images
  have hfne : f p₂ ≠ f q₂ := by
    intro h
    rcases hclean p₂ q₂ hW₂ hW₄ h with h1 | h1 | h1 | h1 | h1
    · have h10 : (0 : ℝ) = 1 := hγ₂inj (by norm_num) (by norm_num) (by rw [hγ₂0, hγ₂1, h1])
      norm_num at h10
    · exact hp₁arc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₂1.trans h1.2⟩
    · exact absurd h1.1 hp₂p₁
    · have h10 : (0 : ℝ) = 1 := hγ₂inj (by norm_num) (by norm_num) (by rw [hγ₂0, hγ₂1, h1.1])
      norm_num at h10
    · exact hq₁arc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₂0.trans h1.1⟩
  have hd0 : A (f q₂) - A (f p₂) ≠ 0 := by
    intro h
    exact hfne (hAl.injective (sub_eq_zero.mp h)).symm
  have hdK : A (f q₂) - A (f p₂) ∈ K := K.sub_mem (hflat q₂ hq₂U) (hflat p₂ hp₂U)
  -- ## the model vector `e₀ = splitE k (1,0)` of the straight arc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k + 1 = n := ⟨n - 1, by omega⟩
  set e₀ : EuclideanSpace ℝ (Fin n) :=
    hk ▸ (splitE k (((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) :
      ℝ × EuclideanSpace ℝ (Fin k))) with he₀def
  have he₀ : e₀ ≠ 0 := by
    rw [he₀def]
    exact cast_splitE_one_ne_zero hk
  have hES : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  -- ## a linear iso `K ≅ ℝⁿ` carrying the arc's chord to `2 e₀`
  obtain ⟨T, hT⟩ := exists_linearEquiv_map_eq_ne_zero (V := ↥K) (W := EuclideanSpace ℝ (Fin n))
    (by rw [hKfin, hES]) (v := (⟨A (f q₂) - A (f p₂), hdK⟩ : ↥K)) (w := (2 : ℝ) • e₀)
    (fun h => hd0 (congrArg Subtype.val h)) (smul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) he₀)
  set TLM : ↥K ≃L[ℝ] EuclideanSpace ℝ (Fin n) := T.toContinuousLinearEquiv with hTLMdef
  have hTLM : TLM (⟨A (f q₂) - A (f p₂), hdK⟩ : ↥K) = (2 : ℝ) • e₀ := hT
  -- ## the coordinate projection `l` of `ℝ^{2n}` onto `K ≅ ℝⁿ`
  set l : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (TLM : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)).comp K.orthogonalProjectionOnto with hldef
  have hlK : ∀ (y : EuclideanSpace ℝ (Fin (2 * n))) (hy : y ∈ K), l y = TLM ⟨y, hy⟩ := by
    intro y hy
    have h1 : K.orthogonalProjectionOnto y = (⟨y, hy⟩ : ↥K) :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨y, hy⟩ : ↥K)
    show TLM (K.orthogonalProjectionOnto y) = TLM ⟨y, hy⟩
    rw [h1]
  -- ## the affine chart map `G`: `l ∘ A ∘ f`, translated so that `γ₂ 0 ↦ -e₀`
  set w : EuclideanSpace ℝ (Fin n) := -e₀ - l (A (f p₂)) with hwdef
  set G : M → EuclideanSpace ℝ (Fin n) := fun z => l (A (f z)) + w with hGdef
  -- ## the left inverse `Ψ` of `G` on `U`
  set B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    K.subtypeL.comp (TLM.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] ↥K) with hBdef
  set Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun ξ => Ainv (B (ξ - w)) with hΨdef
  have hBmem : ∀ z ∈ U, B (l (A (f z))) = A (f z) := by
    intro z hz
    have h3 : l (A (f z)) = TLM ⟨A (f z), hflat z hz⟩ := hlK _ (hflat z hz)
    show K.subtypeL (TLM.symm (l (A (f z)))) = A (f z)
    rw [h3]
    simp
  have hΨG : ∀ z ∈ U, Ψ (G z) = f z := by
    intro z hz
    have h1 : G z - w = l (A (f z)) := by
      show l (A (f z)) + w - w = l (A (f z))
      rw [add_sub_cancel_right]
    show Ainv (B (G z - w)) = f z
    rw [h1, hBmem z hz]
    exact hAl (f z)
  have hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : EuclideanSpace ℝ (Fin n) => B (ξ - w)) :=
      B.contDiff.comp (contDiff_id.sub contDiff_const)
    exact hAinv.comp h1
  have hGsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    have h1 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : M => A (f z)) := hA.contMDiff.comp hf
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => l y + w) := l.contDiff.add contDiff_const
    exact h2.contMDiff.comp h1
  -- ## `mfderiv G` is injective on `U` (via `f = Ψ ∘ G` there)
  have hGimm : ∀ x : M, x ∈ U →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) G x) := by
    intro x hx
    have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    have hev : (fun z : M => Ψ (G z)) =ᶠ[𝓝 x] f := by
      filter_upwards [hUo.mem_nhds hx] with z hz
      exact hΨG z hz
    have hchain : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun z : M => Ψ (G z)) x
        = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) Ψ (G x)).comp
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) G x) :=
      mfderiv_comp x (hΨsm.contMDiff.mdifferentiableAt hne) (hGsm.mdifferentiableAt hne)
    have hmf : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x
        = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) Ψ (G x)).comp
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) G x) := by
      rw [← hev.mfderiv_eq_v433]
      exact hchain
    exact injective_of_comp_injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) G x)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) Ψ (G x))
      (by rw [← hmf]; exact himm x)
  -- ## `f` is injective on the tube
  have hUinj : Set.InjOn f U := by
    intro y hy z hz hyz
    rcases hclean y z (hUW hy) (hUW hz) hyz with h | h | h | h | h
    · exact h
    · exact absurd (h.2 ▸ hz) hp₁U
    · exact absurd (h.1 ▸ hy) hp₁U
    · exact absurd (h.2 ▸ hz) hq₁U
    · exact absurd (h.1 ▸ hy) hq₁U
  have hGinj : Set.InjOn G U := by
    intro y hy z hz hyz
    exact hUinj hy hz (by rw [← hΨG y hy, ← hΨG z hz, hyz])
  -- ## the chart of `M` on the tube
  obtain ⟨c, hcsrc, hceq, hcsm⟩ :=
    exists_smoothChart_of_injOn_immersion_of_nonempty_source G U hUo ⟨p₂, hp₂U⟩
      hGsm hGinj hGimm
  -- ## the arc row
  have harcG : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      G (γ₂ t) = hk ▸ (splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k)))) := by
    intro t ht
    have h1 : A (f (γ₂ t)) = A (f p₂) + t • (A (f q₂) - A (f p₂)) := hrow t ht
    have hlq : l (A (f q₂) - A (f p₂)) = (2 : ℝ) • e₀ := (hlK _ hdK).trans hTLM
    have h2 : l (A (f (γ₂ t))) = l (A (f p₂)) + t • ((2 : ℝ) • e₀) := by
      calc l (A (f (γ₂ t))) = l (A (f p₂) + t • (A (f q₂) - A (f p₂))) := by rw [h1]
        _ = l (A (f p₂)) + t • l (A (f q₂) - A (f p₂)) := by rw [map_add, map_smul]
        _ = l (A (f p₂)) + t • ((2 : ℝ) • e₀) := by rw [hlq]
    calc G (γ₂ t) = (l (A (f p₂)) + w) + t • ((2 : ℝ) • e₀) := by
          show l (A (f (γ₂ t))) + w = _
          rw [h2]
          abel
      _ = -e₀ + t • ((2 : ℝ) • e₀) := by
          congr 1
          show l (A (f p₂)) + w = -e₀
          rw [hwdef]
          abel
      _ = ((2 : ℝ) * t - 1) • e₀ := by
          rw [← neg_one_smul ℝ e₀, smul_smul, ← add_smul]
          congr 1
          ring
      _ = hk ▸ (splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k)))) := by
          rw [he₀def]
          exact (cast_splitE_smul hk (2 * t - 1)).symm
  refine ⟨k, hk, c, hcsm, ?_, ?_, ?_⟩
  · rw [hcsrc]
    exact hUW
  · rw [hcsrc]
    exact hUarc
  · intro t ht
    rw [hceq (γ₂ t) (hUarc ⟨t, ht, rfl⟩)]
    exact harcG t ht

end Work.Drive.PushDisc
