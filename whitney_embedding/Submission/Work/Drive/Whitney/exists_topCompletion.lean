import Mathlib
import Submission.Work.Drive.Whitney.exists_anchoredFrameOfFlagFamily
import Submission.Work.Drive.Whitney.frameExtensionBoundary
import Submission.Work.Drive.Whitney.exists_glExtension
import Submission.Work.Drive.Whitney.exists_globalReparam
import Submission.Work.Drive.Whitney.det_append_eq_mul_det

/-!
# A smooth family of completions of a smooth family of frames

`Work.Drive.Whitney.exists_topCompletion`: given a smooth family `S t` of `k + 2` linearly
independent vectors of a finite-dimensional real inner product space `F` of dimension `(k+2)+k`, a
completion `U₀` of `S a` and of `S b` whose determinants (in a fixed basis `b₀`) have the same sign,
there is a smooth family `U t` of completions of `S t` for `t ∈ [a,b]` with `U t = U₀` off a small
open interval around `[a,b]`.

The proof first solves the theorem in `F = EuclideanSpace ℝ (Fin ((k+2)+k))` with the standard basis
(`exists_topCompletion_euclid`) and then transports it along the coordinate equivalence
`b₀.equivFunL` (`exists_topCompletion`).

The Euclidean case fixes a smooth family `Φ t` of linear isomorphisms whose first `k+2` columns are
`S t` (from `exists_smoothFrame_extension_local`, after the reparametrisation
`exists_globalReparam` makes the family globally independent).  The complement frame is
`N t i = Φ t (e_{k+2+i})`, the coordinates of `U₀` in the basis `(S t, N t)` give the matrix `M t`,
and `det_append_eq_mul_det` shows
`b₀.det (Fin.append (S t) U₀) = b₀.det (Fin.append (S t) (N t)) * (M t).det`.
The sign hypothesis `hdet` therefore forces `0 < (M a).det * (M b).det` (the determinant of the
`N`-frame has constant sign on `[a,b]`), and `exists_glExtension` produces a smooth family `H` of
invertible matrices equal to `M` off a small interval.  The completion is
`U t j = ∑ l, A t l j • S t l + ∑ i, H t i j • N t i`, whose independence follows from
`det_append_eq_mul_det` once more.
-/

namespace Work.Drive.Whitney

open scoped ContDiff

/-- The linear independence criterion in terms of the determinant. -/
lemma topc_linearIndependent_iff_det_ne_zero {F : Type*} [AddCommGroup F] [Module ℝ F] {m : ℕ}
    (b₀ : Module.Basis (Fin m) ℝ F) (v : Fin m → F) :
    LinearIndependent ℝ v ↔ b₀.det v ≠ 0 := by
  rw [← isUnit_iff_ne_zero]
  constructor
  · intro hv
    haveI : Module.Finite ℝ F := Module.Finite.of_basis b₀
    refine (Module.Basis.is_basis_iff_det b₀).mp ⟨hv, ?_⟩
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hv, Fintype.card_fin, Module.finrank_eq_card_basis b₀,
      Fintype.card_fin]
  · intro hu
    exact ((Module.Basis.is_basis_iff_det b₀).mpr hu).1

/-- A continuous real function on a preconnected space which never vanishes has constant sign. -/
lemma topc_mul_pos_of_continuous_ne_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (hne : ∀ x, f x ≠ 0) (x y : X) : 0 < f x * f y := by
  have hord : (Set.range f).OrdConnected := (isPreconnected_range hf).ordConnected
  have key : ∀ {u v : X}, f u < 0 → 0 < f v → False := by
    intro u v hu hv
    have hmem : (0 : ℝ) ∈ Set.range f :=
      hord.out ⟨u, rfl⟩ ⟨v, rfl⟩ ⟨le_of_lt hu, le_of_lt hv⟩
    obtain ⟨z, hz⟩ := hmem
    exact hne z hz
  rcases lt_trichotomy (f x) 0 with hx | hx | hx
  · rcases lt_trichotomy (f y) 0 with hy | hy | hy
    · exact mul_pos_of_neg_of_neg hx hy
    · exact absurd hy (hne y)
    · exact absurd (key hx hy) not_false
  · exact absurd hx (hne x)
  · rcases lt_trichotomy (f y) 0 with hy | hy | hy
    · exact absurd (key hy hx) not_false
    · exact absurd hy (hne y)
    · exact mul_pos hx hy

/-- Expansion of a vector of Euclidean space in the standard basis. -/
lemma topc_sum_single (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    ∑ i : Fin m, x.ofLp i • EuclideanSpace.single i (1 : ℝ) = x := by
  apply WithLp.ofLp_injective 2
  rw [WithLp.ofLp_sum]
  funext j
  rw [Finset.sum_apply]
  simp only [WithLp.ofLp_smul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem exists_topCompletion_euclid {k : ℕ} {a b : ℝ} (hab : a < b)
    (S : ℝ → Fin (k + 2) → EuclideanSpace ℝ (Fin ((k + 2) + k)))
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hindS : ∀ t ∈ Set.Icc a b, LinearIndependent ℝ (S t))
    (U₀ : Fin k → EuclideanSpace ℝ (Fin ((k + 2) + k)))
    (hUa : LinearIndependent ℝ (Fin.append (S a) U₀))
    (hUb : LinearIndependent ℝ (Fin.append (S b) U₀))
    (hdet : 0 < (EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ).toBasis.det (Fin.append (S a) U₀) *
      (EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ).toBasis.det (Fin.append (S b) U₀)) :
    ∃ (δ : ℝ) (_ : 0 < δ) (U : ℝ → Fin k → EuclideanSpace ℝ (Fin ((k + 2) + k))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      (∀ t : ℝ, t ∉ Set.Ioo (a + δ) (b - δ) → U t = U₀) ∧
      (∀ t ∈ Set.Icc a b, LinearIndependent ℝ (Fin.append (S t) (U t))) := by
  classical
  have hkm : k + 2 ≤ (k + 2) + k := by omega
  -- (1) globally independent reparametrisation
  obtain ⟨ψ, hψsm, hψid, hψglob⟩ :=
    exists_globalReparam (m := (k + 2) + k) (r := k + 2) hab S hS hindS
  -- (2) the frame family extending S ∘ ψ
  have hb_ind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (fun i : Fin (k + 2) => S (ψ p.1) i) :=
    fun p => hψglob p.1
  have hb_sm : ∀ i : Fin (k + 2),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => S (ψ p.1) i) := by
    intro i
    exact (contDiff_pi.mp ((hS.comp hψsm).comp contDiff_fst)) i
  obtain ⟨Φb, hΦbsm, hΦbcol⟩ :=
    exists_smoothFrame_extension_local (m := (k + 2) + k) (k := k + 2) hkm
      (fun s _ i => S (ψ s) i) hb_sm hb_ind
  let Φ : ℝ → (EuclideanSpace ℝ (Fin ((k + 2) + k)) ≃L[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k))) :=
    fun t => Φb t 0
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (Φb t 0 : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
        EuclideanSpace ℝ (Fin ((k + 2) + k)))) :=
    hΦbsm.comp (contDiff_id.prodMk contDiff_const)
  have hΦcol : ∀ (t : ℝ) (i : Fin (k + 2)),
      Φ t ((EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ) (Fin.castLE hkm i)) = S (ψ t) i :=
    fun t i => hΦbcol (t, 0) i
  -- (3) the complement frame, the coordinates of U₀, and the two matrices
  let e_std : Fin ((k + 2) + k) → EuclideanSpace ℝ (Fin ((k + 2) + k)) :=
    ⇑(EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ)
  let b₀' : Module.Basis (Fin ((k + 2) + k)) ℝ (EuclideanSpace ℝ (Fin ((k + 2) + k))) :=
    (EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ).toBasis
  let N : ℝ → Fin k → EuclideanSpace ℝ (Fin ((k + 2) + k)) :=
    fun t i => Φ t (e_std (Fin.natAdd (k + 2) i))
  let co : ℝ → Fin k → EuclideanSpace ℝ (Fin ((k + 2) + k)) :=
    fun t i => ((Φ t).symm : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
      EuclideanSpace ℝ (Fin ((k + 2) + k))) (U₀ i)
  let A : ℝ → Matrix (Fin (k + 2)) (Fin k) ℝ :=
    fun t l i => (co t i).ofLp (Fin.castAdd k l)
  let M : ℝ → Matrix (Fin k) (Fin k) ℝ := fun t j i => (co t i).ofLp (Fin.natAdd (k + 2) j)
  have hcosm : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => co t i) := by
    intro i
    have hsymm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => ((Φ t).symm : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
          EuclideanSpace ℝ (Fin ((k + 2) + k)))) := contDiff_symm_of_contDiff Φ hΦsm
    simpa only [co] using (hsymm.clm_apply contDiff_const)
  have hAsm : ∀ (l : Fin (k + 2)) (i : Fin k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => A t l i) := by
    intro l i
    have h1 := (ContinuousLinearMap.contDiff (EuclideanSpace.proj (Fin.castAdd k l))).comp
      (hcosm i)
    exact h1
  have hMsm : ∀ (j : Fin k) (i : Fin k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => M t j i) := by
    intro j i
    have h1 := (ContinuousLinearMap.contDiff (EuclideanSpace.proj (Fin.natAdd (k + 2) j))).comp
      (hcosm i)
    exact h1

  -- (4) the expansion of `co` in the standard basis
  have hcast : ∀ l : Fin (k + 2), (Fin.castLE hkm l : Fin ((k + 2) + k)) = Fin.castAdd k l :=
    fun l => Fin.ext rfl
  have h_expand : ∀ (t : ℝ) (i : Fin k), co t i
      = (∑ l : Fin (k + 2), A t l i • e_std (Fin.castAdd k l))
        + (∑ j : Fin k, M t j i • e_std (Fin.natAdd (k + 2) j)) := by
    intro t i
    have h := topc_sum_single ((k + 2) + k) (co t i)
    rw [Fin.sum_univ_add] at h
    rw [← h]
    simp only [A, M, e_std, EuclideanSpace.basisFun_apply]
  -- (5) the identity satisfied by `U₀`
  have hU0 : ∀ (t : ℝ) (i : Fin k), U₀ i
      = (∑ l : Fin (k + 2), A t l i • S (ψ t) l) + (∑ j : Fin k, M t j i • N t j) := by
    intro t i
    have hterm1 : ∀ l : Fin (k + 2),
        Φ t (A t l i • e_std (Fin.castAdd k l)) = A t l i • S (ψ t) l := by
      intro l
      rw [map_smul]
      congr 1
      rw [← hcast l]
      exact hΦcol t l
    have hterm2 : ∀ j : Fin k,
        Φ t (M t j i • e_std (Fin.natAdd (k + 2) j)) = M t j i • N t j := by
      intro j
      rw [map_smul]
    calc U₀ i = Φ t (co t i) := (ContinuousLinearEquiv.apply_symm_apply (Φ t) (U₀ i)).symm
      _ = Φ t ((∑ l : Fin (k + 2), A t l i • e_std (Fin.castAdd k l))
            + (∑ j : Fin k, M t j i • e_std (Fin.natAdd (k + 2) j))) := by rw [h_expand t i]
      _ = Φ t (∑ l : Fin (k + 2), A t l i • e_std (Fin.castAdd k l))
            + Φ t (∑ j : Fin k, M t j i • e_std (Fin.natAdd (k + 2) j)) := by rw [map_add]
      _ = (∑ l : Fin (k + 2), A t l i • S (ψ t) l) + (∑ j : Fin k, M t j i • N t j) := by
          rw [map_sum, map_sum]
          exact congrArg₂ HAdd.hAdd (Finset.sum_congr rfl (fun l _ => hterm1 l))
            (Finset.sum_congr rfl (fun j _ => hterm2 j))
  -- (6) the family `(S (ψ t), N t)` is a basis at every `t`
  have hΦe : ∀ t : ℝ, (Fin.append (fun l : Fin (k + 2) => S (ψ t) l) (N t))
      = fun j : Fin ((k + 2) + k) => Φ t (e_std j) := by
    intro t
    funext j
    refine Fin.addCases (fun l => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      show S (ψ t) l = Φ t (e_std (Fin.castAdd k l))
      rw [← hcast l]
      exact (hΦcol t l).symm
    · rw [Fin.append_right]
  have hNli : ∀ t : ℝ, LinearIndependent ℝ (Fin.append (fun l => S (ψ t) l) (N t)) := by
    intro t
    rw [hΦe t]
    exact (b₀'.linearIndependent).map'
      ((Φ t).toLinearMap) (by
        rw [LinearMap.ker_eq_bot]
        exact (Φ t).injective)
  have hNli' : ∀ t ∈ Set.Icc a b, LinearIndependent ℝ (Fin.append (S t) (N t)) := by
    intro t ht
    have h := hNli t
    rwa [hψid t ht] at h
  -- the determinant of the `N`-frame is continuous and nowhere zero
  have hNcont : Continuous (fun t : ℝ =>
      LinearMap.det ((((Φ t : EuclideanSpace ℝ (Fin ((k + 2) + k)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin ((k + 2) + k))) : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
          EuclideanSpace ℝ (Fin ((k + 2) + k))) :
        EuclideanSpace ℝ (Fin ((k + 2) + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k))))) :=
    (ContinuousLinearMap.continuous_det).comp (hΦsm.continuous)
  have hNsign : 0 < (b₀'.det
        (Fin.append (S a) (N a))) *
      (b₀'.det (Fin.append (S b) (N b))) := by
    have hfun : (fun t : ℝ => b₀'.det
        (Fin.append (fun l => S (ψ t) l) (N t)))
        = fun t : ℝ => LinearMap.det ((((Φ t : EuclideanSpace ℝ (Fin ((k + 2) + k)) ≃L[ℝ]
            EuclideanSpace ℝ (Fin ((k + 2) + k))) : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
              EuclideanSpace ℝ (Fin ((k + 2) + k))) :
            EuclideanSpace ℝ (Fin ((k + 2) + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k))))
          * b₀'.det e_std := by
      funext t
      rw [hΦe t]
      rw [show (fun j : Fin ((k + 2) + k) => Φ t (e_std j))
          = ⇑((((Φ t : EuclideanSpace ℝ (Fin ((k + 2) + k)) ≃L[ℝ]
              EuclideanSpace ℝ (Fin ((k + 2) + k))) : EuclideanSpace ℝ (Fin ((k + 2) + k)) →L[ℝ]
                EuclideanSpace ℝ (Fin ((k + 2) + k))) :
              EuclideanSpace ℝ (Fin ((k + 2) + k)) →ₗ[ℝ]
                EuclideanSpace ℝ (Fin ((k + 2) + k)))) ∘ e_std from rfl]
      exact Module.Basis.det_comp _ _ e_std
    have hne : ∀ t : ℝ, b₀'.det
        (Fin.append (fun l => S (ψ t) l) (N t)) ≠ 0 :=
      fun t => (topc_linearIndependent_iff_det_ne_zero b₀' _).mp (hNli t)
    have hmain := topc_mul_pos_of_continuous_ne_zero (f := fun t : ℝ =>
      b₀'.det
        (Fin.append (fun l => S (ψ t) l) (N t)))
      (by rw [hfun]; exact (hNcont.mul continuous_const)) hne a b
    rwa [hψid a ⟨le_refl a, le_of_lt hab⟩, hψid b ⟨le_of_lt hab, le_refl b⟩] at hmain
  -- (7) determinant relation for `U₀`
  have hdetU0 : ∀ t ∈ Set.Icc a b,
      b₀'.det (Fin.append (S t) U₀)
        = b₀'.det (Fin.append (S t) (N t))
          * (M t).det := by
    intro t ht
    have hψt : ψ t = t := hψid t ht
    have hli := hNli' t ht
    have hU : ∀ j : Fin k, U₀ j
        = (∑ l : Fin (k + 2), A t l j • (S t) l) + (∑ i : Fin k, M t i j • (N t) i) := by
      intro j
      have h := hU0 t j
      rwa [hψt] at h
    exact det_append_eq_mul_det (v := S t) (n := N t) b₀' hli U₀ (M t) (A t) hU
  -- (8) the two end determinants of `M`
  have hMa : (M a).det ≠ 0 := by
    have h := hdetU0 a ⟨le_refl a, le_of_lt hab⟩
    have hd : b₀'.det (Fin.append (S a) U₀)
        ≠ 0 := (topc_linearIndependent_iff_det_ne_zero b₀' _).mp hUa
    have hn : b₀'.det
        (Fin.append (S a) (N a)) ≠ 0 :=
      (topc_linearIndependent_iff_det_ne_zero b₀' _).mp (hNli' a ⟨le_refl a, le_of_lt hab⟩)
    intro h0
    rw [h0, mul_zero] at h
    exact hd h
  have hMb : (M b).det ≠ 0 := by
    have h := hdetU0 b ⟨le_of_lt hab, le_refl b⟩
    have hd : b₀'.det (Fin.append (S b) U₀)
        ≠ 0 := (topc_linearIndependent_iff_det_ne_zero b₀' _).mp hUb
    have hn : b₀'.det
        (Fin.append (S b) (N b)) ≠ 0 :=
      (topc_linearIndependent_iff_det_ne_zero b₀' _).mp (hNli' b ⟨le_of_lt hab, le_refl b⟩)
    intro h0
    rw [h0, mul_zero] at h
    exact hd h
  have hMsign : 0 < (M a).det * (M b).det := by
    have h1 : 0 < (b₀'.det
        (Fin.append (S a) (N a)) * (M a).det) *
        (b₀'.det (Fin.append (S b) (N b))
          * (M b).det) := by
      rw [← hdetU0 a ⟨le_refl a, le_of_lt hab⟩, ← hdetU0 b ⟨le_of_lt hab, le_refl b⟩]
      exact hdet
    nlinarith [hNsign, h1]
  -- (9) the extension of `M` off the interval
  obtain ⟨δ, hδ, H, hHsm, hHeq, hHdet⟩ := exists_glExtension hab M hMsm hMa hMb hMsign
  let U : ℝ → Fin k → EuclideanSpace ℝ (Fin ((k + 2) + k)) := fun t j =>
    (∑ l : Fin (k + 2), A t l j • S (ψ t) l) + (∑ i : Fin k, H t i j • N t i)
  refine ⟨δ, hδ, U, ?_, ?_, ?_⟩
  · -- smoothness
    refine contDiff_pi.mpr (fun j => ?_)
    have hSψ : ∀ l : Fin (k + 2), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => S (ψ t) l) := fun l => (contDiff_pi.mp (hS.comp hψsm)) l
    have hNsm : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => N t i) := by
      intro i
      have h := hΦsm.clm_apply (contDiff_const (c := e_std (Fin.natAdd (k + 2) i)))
      convert h using 1
      funext t
      rfl
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => ∑ l : Fin (k + 2), A t l j • S (ψ t) l) :=
      ContDiff.sum (fun l _ => (hAsm l j).smul (hSψ l))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => ∑ i : Fin k, H t i j • N t i) :=
      ContDiff.sum (fun i _ => (hHsm i j).smul (hNsm i))
    have h3 := h1.add h2
    simpa only [U] using h3
  · -- the support condition
    intro t ht
    funext j
    have hH : H t = M t := hHeq t ht
    simp only [U]
    rw [hH]
    exact (hU0 t j).symm
  · -- linear independence on `[a,b]`
    intro t ht
    have hψt : ψ t = t := hψid t ht
    have hU : ∀ j : Fin k, U t j
        = (∑ l : Fin (k + 2), A t l j • (S t) l) + (∑ i : Fin k, H t i j • (N t) i) := by
      intro j
      simp only [U]
      rw [hψt]
    have hdetU : b₀'.det (Fin.append (S t) (U t))
        = b₀'.det (Fin.append (S t) (N t))
          * (H t).det := det_append_eq_mul_det (v := S t) (n := N t) b₀' (hNli' t ht) (U t) (H t) (A t) hU
    refine (topc_linearIndependent_iff_det_ne_zero b₀' _).mpr ?_
    rw [hdetU]
    exact mul_ne_zero ((topc_linearIndependent_iff_det_ne_zero b₀' _).mp (hNli' t ht)) (hHdet t ht)


/-- Comparing the two `det` maps along a linear map: they differ by a constant factor. -/
lemma topc_det_comp_eq {F E : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b₀ : Module.Basis ι ℝ F) (b₁ : Module.Basis ι ℝ E)
    (e : F →ₗ[ℝ] E) (v : ι → F) :
    b₁.det (fun i => e (v i)) = (b₁.det (fun i => e (b₀ i))) * b₀.det v := by
  have h := AlternatingMap.eq_smul_basis_det (R := ℝ) b₀ (b₁.det.compLinearMap e)
  have h2 := congrArg (fun f => f v) h
  simp only [AlternatingMap.smul_apply, smul_eq_mul, AlternatingMap.compLinearMap_apply] at h2
  exact h2

theorem exists_topCompletion {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {k : ℕ} (b₀ : Module.Basis (Fin ((k + 2) + k)) ℝ F)
    {a b : ℝ} (hab : a < b)
    (S : ℝ → Fin (k + 2) → F) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hindS : ∀ t ∈ Set.Icc a b, LinearIndependent ℝ (S t))
    (U₀ : Fin k → F)
    (hUa : LinearIndependent ℝ (Fin.append (S a) U₀))
    (hUb : LinearIndependent ℝ (Fin.append (S b) U₀))
    (hdet : 0 < b₀.det (Fin.append (S a) U₀) * b₀.det (Fin.append (S b) U₀)) :
    ∃ (δ : ℝ) (_ : 0 < δ) (U : ℝ → Fin k → F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      (∀ t : ℝ, t ∉ Set.Ioo (a + δ) (b - δ) → U t = U₀) ∧
      (∀ t ∈ Set.Icc a b, LinearIndependent ℝ (Fin.append (S t) (U t))) := by
  classical
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k)) :=
    b₀.equivFunL.trans (EuclideanSpace.equiv (Fin ((k + 2) + k)) ℝ).symm
  let b₁ : Module.Basis (Fin ((k + 2) + k)) ℝ (EuclideanSpace ℝ (Fin ((k + 2) + k))) :=
    (EuclideanSpace.basisFun (Fin ((k + 2) + k)) ℝ).toBasis
  set c : ℝ := b₁.det (fun j => e (b₀ j)) with hc_def
  have hdetrel : ∀ v : Fin ((k + 2) + k) → F, b₁.det (fun j => e (v j)) = c * b₀.det v := by
    intro v
    rw [hc_def]
    exact topc_det_comp_eq b₀ b₁ (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k))) v
  have hc : c ≠ 0 := by
    rw [hc_def]
    refine (topc_linearIndependent_iff_det_ne_zero b₁ _).mp ?_
    exact b₀.linearIndependent.map' (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k)))
      (by rw [LinearMap.ker_eq_bot]; exact e.injective)
  have happ : ∀ (v : Fin (k + 2) → F) (w : Fin k → F),
      Fin.append (fun j => e (v j)) (fun i => e (w i)) = fun i => e (Fin.append v w i) := by
    intro v w
    funext i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · rw [Fin.append_left, Fin.append_left]
    · rw [Fin.append_right, Fin.append_right]
  have hS' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => fun j : Fin (k + 2) => e (S t j)) :=
    contDiff_pi.mpr (fun j => (e.contDiff).comp ((contDiff_pi.mp hS) j))
  have hindS' : ∀ t ∈ Set.Icc a b,
      LinearIndependent ℝ (fun j : Fin (k + 2) => e (S t j)) := fun t ht =>
    (hindS t ht).map' (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k)))
      (by rw [LinearMap.ker_eq_bot]; exact e.injective)
  have hUa' : LinearIndependent ℝ
      (Fin.append (fun j => e (S a j)) (fun i => e (U₀ i))) := by
    rw [happ (S a) U₀]
    exact hUa.map' (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k)))
      (by rw [LinearMap.ker_eq_bot]; exact e.injective)
  have hUb' : LinearIndependent ℝ
      (Fin.append (fun j => e (S b j)) (fun i => e (U₀ i))) := by
    rw [happ (S b) U₀]
    exact hUb.map' (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin ((k + 2) + k)))
      (by rw [LinearMap.ker_eq_bot]; exact e.injective)
  have hdet' : 0 < b₁.det (Fin.append (fun j => e (S a j)) (fun i => e (U₀ i))) *
      b₁.det (Fin.append (fun j => e (S b j)) (fun i => e (U₀ i))) := by
    rw [happ (S a) U₀, happ (S b) U₀, hdetrel (Fin.append (S a) U₀),
      hdetrel (Fin.append (S b) U₀)]
    nlinarith [hdet, mul_self_pos.mpr hc]
  obtain ⟨δ, hδ, U', hU'sm, hU'supp, hU'ind⟩ :=
    exists_topCompletion_euclid hab (fun t j => e (S t j)) hS' hindS' (fun i => e (U₀ i))
      hUa' hUb' hdet'
  let U : ℝ → Fin k → F := fun t i => e.symm (U' t i)
  refine ⟨δ, hδ, U, ?_, ?_, ?_⟩
  · refine contDiff_pi.mpr (fun i => ?_)
    exact (e.symm.contDiff).comp ((contDiff_pi.mp hU'sm) i)
  · intro t ht
    funext i
    simp only [U]
    rw [hU'supp t ht]
    exact ContinuousLinearEquiv.symm_apply_apply e (U₀ i)
  · intro t ht
    have hfam : Fin.append (fun j => e (S t j)) (U' t)
        = fun i => e (Fin.append (S t) (U t) i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun l => ?_) i
      · rw [Fin.append_left, Fin.append_left]
      · rw [Fin.append_right, Fin.append_right]
        simp only [U, ContinuousLinearEquiv.apply_symm_apply]
    have h1 := hU'ind t ht
    rw [hfam] at h1
    refine (topc_linearIndependent_iff_det_ne_zero b₀ _).mpr ?_
    intro h0
    have hb₁ : b₁.det (fun j => e (Fin.append (S t) (U t) j)) ≠ 0 :=
      (topc_linearIndependent_iff_det_ne_zero b₁ _).mp h1
    rw [hdetrel (Fin.append (S t) (U t)), h0, mul_zero] at hb₁
    exact hb₁ rfl

end Work.Drive.Whitney
