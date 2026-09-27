import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.Whitney.exists_topCompletion
import Submission.Work.Drive.Whitney.exists_injective_fill
import Submission.Work.Drive.Whitney.exists_complement_fromEdge
import Submission.Work.Drive.Whitney.appendMapInjective
import Submission.Work.Drive.PushDisc.tupleLiDropMiddle
import Submission.Work.Drive.PushDisc.tupleLiSwap
import Submission.Work.Drive.PushDisc.contDiffRecipOneSubSq
import Submission.Work.Drive.PushDisc.detProductSignCast

/-!
# The two frames of the framing chart of the Milnor route

`Work.Drive.PushDisc.lensFrames`: the existence of the two frames `U`, `W` of the framing chart,
with the two prescribed rows `U (x,0) = ιu` (the plane row) and `W (x, arch x) = V x` (the finger
row) and the frame row `[∂ₓ, ∂_y, U, W]` independent on the lens `lensK`.

The proof is the one described in the module docstring of `lensFrames`:

* the frame family is first transported along the linear identification
  `T : Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k))` supplied by the sign hypothesis, because the
  three engines (`exists_topCompletion`, `exists_injective_fill`, `exists_complement_fromEdge`) live
  on a *finite-dimensional real inner product space*, and `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` carries only
  the product (sup) norm, which is not induced by an inner product;
* `exists_topCompletion` completes the top-edge frame `[∂ₓ, ∂_y, V]` to a frame
  `[∂ₓ, ∂_y, V, U_top]`, with `U_top = ιu` off a compact subinterval of `(-1,1)`.  This is where the
  sign hypothesis is spent (`detProductSignCast` turns the two corner determinants of the statement
  into the two determinants needed by the engine, and `topc_linearIndependent_iff_det_ne_zero` turns
  them into the two corner independence rows);
* an interpolant `Ubase` is built from `U_top` and the constant frame `ιu`, using a smooth extension
  `g` of `y ↦ (1 - y)⁻¹` (`contDiffRecipOneSubSq`) as the interpolation weight: `Ubase (x,0) = ιu`
  and `Ubase (x, arch x) = U_top x` on `|x| ≤ 1`
  (the weight `y * g y` vanishes at `y = 0` and equals `1` on the arch range);
* `exists_injective_fill` perturbs the interior of the interpolant by `β p • w` with a *single*
  vector `w`, `β p = p.2 * (arch p.1 - p.2)` vanishing exactly on the boundary of the lens, making
  `[∂ₓ, ∂_y, U]` independent on the lens while preserving both boundary rows;
* `exists_complement_fromEdge` transports the prescribed finger row `V` down from the top edge,
  producing `W` with `W (x, arch x) = V x` and `[∂ₓ, ∂_y, U, W]` independent on the lens;
* finally everything is transported back through `T.symm`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

noncomputable section

private abbrev Cin : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The Euclidean model space of the target dimension `2 + k + k`. -/
abbrev lfE (k : ℕ) : Type := EuclideanSpace ℝ (Fin (2 + k + k))

/-- The top edge frame `[∂ₓ, ∂_y, V]`, as a `(2+k)`-tuple. -/
def lfTopF (k : ℕ) (dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k) (t : ℝ) : Fin (2 + k) → Work.Drive.Whitney.Mdl k :=
  Fin.append (planeFrame k dx dy (t, arch t)) (V t)

/-- Composing a tuple with a function commutes with `Fin.append`. -/
theorem lf_append_comp {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] {m n : ℕ} (f : M → N)
    (a : Fin m → M) (b : Fin n → M) :
    Fin.append (f ∘ a) (f ∘ b) = f ∘ Fin.append a b := by
  funext i
  revert i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) <;> simp [Fin.append]

/-- **The two frames of the framing chart** (`lensK` = the lens `{|x| ≤ 1, 0 ≤ y ≤ 1 - x²}`).

`dx`, `dy` are the two partial derivative fields of the disc approximation `Δ` (they are the
`fderiv ℝ Δ p (1,0)` and `fderiv ℝ Δ p (0,1)` of the consumer) and `V x` is the finger's `v`-frame
at the top edge.  The conclusion is the pair of frames `U`, `W` of the framing chart

    θ (x,y,u,v) = Δ (x,y) + U (x,y) u + r W (x,y) v + [S₂ (x, r v) - Δ (x, c x) - r V x v],

with the two *prescribed* rows `U (x,0) = ιu` (the plane row of θ) and `W (x, arch x) = V x` (the
finger row of θ), and the frame row `[∂ₓ, ∂_y, U, W]` independent on `lensK` (which makes θ a local
diffeomorphism there).

Construction: `Work.Drive.Whitney.exists_topCompletion` (L2, with the sign hypothesis `hsign`)
produces `U` along the top edge, equal to `ιu` off a compact subinterval — this is where the
framing obstruction, i.e. the *opposite-sign* hypothesis of the target, is spent;
`Work.Drive.Whitney.exists_injective_fill` (L3) fills it over the lens (using `k + 4 ≤ 2k + 2`,
i.e. `k ≥ 2`), and `Work.Drive.Whitney.exists_complement_fromEdge` (L4) transports `W` down from the
top edge.

The sign hypothesis is stated as the existence of a linear identification `T` of the model space
with `ℝ^(2k+2)` making the product of the two corner determinants positive; since
`det (T ∘ F) = det T · det F`, the *sign* of that product is independent of `T`, so this is a
statement about the configuration only. -/
theorem lensFrames {k : ℕ} (hk : 2 ≤ k)
    (dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hdx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dx)
    (hdy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dy)
    (himm : ∀ p ∈ Work.Drive.PushDisc.lensK,
      LinearIndependent ℝ (Work.Drive.PushDisc.planeFrame k dx dy p))
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (htop : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → LinearIndependent ℝ
      (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy (x, Work.Drive.PushDisc.arch x)) (V x)))
    (hbot : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → LinearIndependent ℝ
      (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy (x, 0)) (Work.Drive.PushDisc.iotaU k)))
    (hsign : ∃ T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)),
      0 < Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame dx dy V (-1))
        * Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame dx dy V 1)) :
    ∃ U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      (∀ x : ℝ, U (x, 0) = Work.Drive.PushDisc.iotaU k) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → W (x, Work.Drive.PushDisc.arch x) = V x) ∧
      (∀ p ∈ Work.Drive.PushDisc.lensK, LinearIndependent ℝ
        (Fin.append (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy p) (U p)) (W p))) := by
  classical
  -- ======================= dimension counts =======================
  have hfinE : Module.finrank ℝ (lfE k) = 2 + k + k := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hdimE : k + 4 ≤ Module.finrank ℝ (lfE k) := by rw [hfinE]; omega
  -- ======================= the linear equivalence =======================
  obtain ⟨T, hT⟩ := hsign
  let TE : Work.Drive.Whitney.Mdl k →ₗ[ℝ] lfE k := (T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] lfE k).toLinearMap
  have hTinj : Function.Injective TE := fun x y h => T.injective h
  have hTker : TE.ker = ⊥ := LinearMap.ker_eq_bot.mpr hTinj
  have hTE_sm : ContDiff ℝ Cin (fun x : Work.Drive.Whitney.Mdl k => TE x) :=
    (LinearMap.toContinuousLinearMap TE).contDiff
  have hTEs_sm : ContDiff ℝ Cin (fun y : lfE k => T.symm y) :=
    (LinearMap.toContinuousLinearMap
      (T.symm : lfE k →ₗ[ℝ] Work.Drive.Whitney.Mdl k)).contDiff
  -- ======================= transporting the hypotheses =======================
  have harch_sm : ContDiff ℝ Cin arch := by
    rw [show arch = fun x : ℝ => 1 - x ^ 2 from rfl]; fun_prop
  have hpf_sm : ContDiff ℝ Cin (planeFrame k dx dy) := by
    refine contDiff_pi.mpr (fun j => ?_)
    have hfun : (fun p : ℝ × ℝ => planeFrame k dx dy p j)
        = (if (j : ℕ) = 0 then (fun p : ℝ × ℝ => dx p) else (fun p : ℝ × ℝ => dy p)) := by
      funext p
      fin_cases j <;> simp [planeFrame]
    rw [hfun]
    by_cases h : (j : ℕ) = 0
    · rw [if_pos h]; exact hdx
    · rw [if_neg h]; exact hdy
  let pfE : ℝ × ℝ → Fin 2 → lfE k := fun p => TE ∘ planeFrame k dx dy p
  let VE : ℝ → Fin k → lfE k := fun x => TE ∘ V x
  let iUE : Fin k → lfE k := TE ∘ iotaU k
  have hpfE_sm : ContDiff ℝ Cin pfE := by
    refine contDiff_pi.mpr (fun j => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp hpf_sm) j)
  have hVE_sm : ContDiff ℝ Cin VE := by
    refine contDiff_pi.mpr (fun j => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp hV) j)
  have himmE : ∀ p ∈ lensK, LinearIndependent ℝ (pfE p) := by
    intro p hp
    exact LinearIndependent.map' (himm p hp) TE hTker
  have htopE : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      LinearIndependent ℝ (Fin.append (pfE (x, arch x)) (VE x)) := by
    intro x hx
    exact (Work.Drive.Whitney.appendMapInjective TE hTinj (planeFrame k dx dy (x, arch x))
      (V x)).mpr (htop x hx)
  have hbotE : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      LinearIndependent ℝ (Fin.append (pfE (x, 0)) iUE) := by
    intro x hx
    exact (Work.Drive.Whitney.appendMapInjective TE hTinj (planeFrame k dx dy (x, 0))
      (iotaU k)).mpr (hbot x hx)
  -- ======================= the top-edge family =======================
  have hTopF_sm : ContDiff ℝ Cin (fun t : ℝ => lfTopF k dx dy V t) := by
    refine contDiff_pi.mpr (fun j => ?_)
    induction j using Fin.addCases with
    | left j' =>
        have hfun : (fun t : ℝ => lfTopF k dx dy V t (Fin.castAdd k j'))
            = (fun t : ℝ => planeFrame k dx dy (t, arch t) j') := by
          funext t; simp [lfTopF, Fin.append_left]
        rw [hfun]
        exact ((contDiff_pi.mp hpf_sm) j').comp (ContDiff.prodMk contDiff_id harch_sm)
    | right j' =>
        have hfun : (fun t : ℝ => lfTopF k dx dy V t (Fin.natAdd 2 j'))
            = (fun t : ℝ => V t j') := by
          funext t; simp [lfTopF, Fin.append_right]
        rw [hfun]
        exact (contDiff_pi.mp hV) j'
  have h2 : k + 2 = 2 + k := by omega
  have hMM : (k + 2) + k = 2 + k + k := by rw [h2]
  let SE : ℝ → Fin (k + 2) → lfE k := fun t => TE ∘ (lfTopF k dx dy V t ∘ Fin.cast h2)
  have hSE_sm : ContDiff ℝ Cin SE := by
    refine contDiff_pi.mpr (fun i => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp hTopF_sm) (Fin.cast h2 i))
  have hSE_ind : ∀ t ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ (SE t) := by
    intro t ht
    exact LinearIndependent.map' (LinearIndependent.comp (htop t ht) (Fin.cast h2)
      (Fin.cast_injective h2)) TE hTker
  -- ======================= the corner determinants =======================
  let b₀E : Module.Basis (Fin ((k + 2) + k)) ℝ (lfE k) :=
    (EuclideanSpace.basisFun (Fin (2 + k + k)) ℝ).toBasis.reindex
      (finCongr (by omega : 2 + k + k = (k + 2) + k))
  have hAeqE : ∀ x : ℝ, Fin.append (SE x) iUE
      = (fun i => T (cornerFrame dx dy V x i)) ∘ Fin.cast hMM := by
    intro x
    have h1 : Fin.append (SE x) iUE = Fin.append (TE ∘ lfTopF k dx dy V x) iUE
        ∘ Fin.cast hMM := by
      have := Fin.append_cast_left (TE ∘ lfTopF k dx dy V x) iUE (k + 2) h2
      simpa only [SE, Function.comp_assoc] using this
    have h2' : Fin.append (TE ∘ lfTopF k dx dy V x) iUE
        = TE ∘ Fin.append (Fin.append (planeFrame k dx dy (x, arch x)) (V x)) (iotaU k) := by
      rw [show lfTopF k dx dy V x = Fin.append (planeFrame k dx dy (x, arch x)) (V x) from rfl,
        lf_append_comp]
    have h3 : TE ∘ Fin.append (Fin.append (planeFrame k dx dy (x, arch x)) (V x)) (iotaU k)
        = (fun i => T (cornerFrame dx dy V x i)) := by
      funext i
      rfl
    rw [h1, h2', h3]
  have hdetE : 0 < b₀E.det (Fin.append (SE (-1)) iUE) * b₀E.det (Fin.append (SE 1) iUE) := by
    have hT' : 0 < Matrix.det
          (fun i j => (T (cornerFrame dx dy V (-1) i)).ofLp j) *
        Matrix.det (fun i j => (T (cornerFrame dx dy V 1 i)).ofLp j) := by
      simpa only [frameDet] using hT
    have h := (detProductSignCast hMM (LinearEquiv.refl ℝ (lfE k)) b₀E
      (fun i => T (cornerFrame dx dy V (-1) i))
      (fun i => T (cornerFrame dx dy V 1 i))).mp hT'
    rwa [← hAeqE (-1), ← hAeqE 1] at h
  have hUaE : LinearIndependent ℝ (Fin.append (SE (-1)) iUE) := by
    refine (Work.Drive.Whitney.topc_linearIndependent_iff_det_ne_zero b₀E _).mpr ?_
    intro h0; rw [h0, zero_mul] at hdetE; exact lt_irrefl _ hdetE
  have hUbE : LinearIndependent ℝ (Fin.append (SE 1) iUE) := by
    refine (Work.Drive.Whitney.topc_linearIndependent_iff_det_ne_zero b₀E _).mpr ?_
    intro h0; rw [h0, mul_zero] at hdetE; exact lt_irrefl _ hdetE
  -- ======================= the top completion =======================
  obtain ⟨δ, hδ, U_topE, hU_topE_sm, hU_topE_supp, hU_topE_ind⟩ :=
    Work.Drive.Whitney.exists_topCompletion b₀E (a := -1) (b := 1) (by norm_num) SE hSE_sm
      hSE_ind iUE hUaE hUbE hdetE
  -- ======================= the two consequences at the top edge =======================
  have hBigE : ∀ x : ℝ, |x| ≤ 1 → LinearIndependent ℝ
      (Fin.append (Fin.append (pfE (x, arch x)) (VE x)) (U_topE x)) := by
    intro x hx
    have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hx)
    have hind := hU_topE_ind x hxI
    have hcast : Fin.append (SE x) (U_topE x)
        = (Fin.append (Fin.append (pfE (x, arch x)) (VE x)) (U_topE x)) ∘ Fin.cast hMM := by
      have h1 : Fin.append (SE x) (U_topE x)
          = Fin.append (TE ∘ lfTopF k dx dy V x) (U_topE x) ∘ Fin.cast hMM := by
        have := Fin.append_cast_left (TE ∘ lfTopF k dx dy V x) (U_topE x) (k + 2) h2
        simpa only [SE, Function.comp_assoc] using this
      rw [h1]
      have h2' : Fin.append (TE ∘ lfTopF k dx dy V x) (U_topE x)
          = (Fin.append (Fin.append (pfE (x, arch x)) (VE x)) (U_topE x)) := by
        rw [show lfTopF k dx dy V x = Fin.append (planeFrame k dx dy (x, arch x)) (V x) from rfl,
          lf_append_comp]
      rw [h2']
    have h2'' : LinearIndependent ℝ
        ((Fin.append (Fin.append (pfE (x, arch x)) (VE x)) (U_topE x)) ∘ Fin.cast hMM) := by
      rw [← hcast]; exact hind
    exact (linearIndependent_equiv (finCongr hMM)
      (f := Fin.append (Fin.append (pfE (x, arch x)) (VE x)) (U_topE x))).mp h2''
  have hliTopE : ∀ x : ℝ, |x| ≤ 1 → LinearIndependent ℝ
      (Fin.append (pfE (x, arch x)) (U_topE x)) :=
    fun x hx => tupleLiDropMiddle _ _ _ (hBigE x hx)
  have hXE : ∀ x : ℝ, |x| ≤ 1 → LinearIndependent ℝ
      (Fin.append (Fin.append (pfE (x, arch x)) (U_topE x)) (VE x)) :=
    fun x hx => tupleLiSwap _ _ _ (hBigE x hx)
  -- ======================= the interpolation down to the bottom edge =======================
  have hr1 : max 0 (1 - δ) < 1 := max_lt (by norm_num) (by linarith)
  obtain ⟨g, hg_sm, hg_val⟩ := contDiffRecipOneSubSq (max 0 (1 - δ)) (le_max_left _ _) hr1
  let UbaseE : ℝ × ℝ → Fin k → lfE k :=
    fun p i => iUE i + (p.2 * g p.1) • (U_topE p.1 i - iUE i)
  have hUbaseE_sm : ContDiff ℝ Cin UbaseE := by
    refine contDiff_pi.mpr (fun i => ?_)
    have h1 : ContDiff ℝ Cin (fun p : ℝ × ℝ => p.2 * g p.1) :=
      contDiff_snd.mul (hg_sm.comp contDiff_fst)
    have h2 : ContDiff ℝ Cin (fun p : ℝ × ℝ => U_topE p.1 i - iUE i) :=
      (((contDiff_pi.mp hU_topE_sm) i).comp contDiff_fst).sub contDiff_const
    exact (contDiff_const (c := iUE i)).add (h1.smul h2)
  have hUbaseE_bot : ∀ x : ℝ, UbaseE (x, 0) = iUE := by
    intro x
    funext i
    simp [UbaseE]
  have hUbaseE_top : ∀ x : ℝ, |x| ≤ 1 → UbaseE (x, arch x) = U_topE x := by
    intro x hx
    by_cases hmem : x ∈ Set.Ioo (-1 + δ) (1 - δ)
    · obtain ⟨hlo, hhi⟩ := hmem
      have hxlt : |x| < 1 - δ := by
        have hδ1 : δ < 1 := by linarith
        rw [abs_lt]
        constructor <;> linarith
      have hxr : |x| ≤ max 0 (1 - δ) := by
        rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - δ)]
        exact le_of_lt hxlt
      have hgx : g x = (1 - x ^ 2)⁻¹ := hg_val x (Set.mem_Icc.mpr (abs_le.mp hxr))
      have hcoef : arch x * g x = 1 := by
        rw [hgx]
        exact mul_inv_cancel₀ (ne_of_gt (arch_pos (by have := abs_nonneg x; linarith)))
      funext i
      simp only [UbaseE, hcoef, one_smul]
      abel
    · have hUt : U_topE x = iUE := hU_topE_supp x hmem
      funext i
      simp only [UbaseE, hUt, sub_self, smul_zero, add_zero]
  -- ======================= filling the frame over the lens =======================
  let β : ℝ × ℝ → ℝ := fun p => p.2 * (arch p.1 - p.2)
  have hβ_sm : ContDiff ℝ Cin β := by
    rw [show β = fun p : ℝ × ℝ => p.2 * (arch p.1 - p.2) from rfl]
    exact contDiff_snd.mul ((harch_sm.comp contDiff_fst).sub contDiff_snd)
  have hindUE : ∀ p ∈ lensK, β p = 0 →
      LinearIndependent ℝ (Fin.append (pfE p) (UbaseE p)) := by
    intro p hp hβp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have hpI : |p.1| ≤ 1 := hp1
    rcases mul_eq_zero.mp hβp with h2' | h2'
    · have hpe : p = (p.1, 0) := Prod.ext rfl h2'
      rw [hpe, hUbaseE_bot p.1]
      exact hbotE p.1 (Set.mem_Icc.mpr (abs_le.mp hpI))
    · have hval : p.2 = arch p.1 := by linarith
      have hpe : p = (p.1, arch p.1) := Prod.ext rfl hval
      rw [hpe, hUbaseE_top p.1 hpI]
      exact hliTopE p.1 hpI
  obtain ⟨wE, hwE⟩ := Work.Drive.Whitney.exists_injective_fill hdimE isCompact_lensK
    pfE hpfE_sm himmE UbaseE hUbaseE_sm β hβ_sm hindUE
  let UE : ℝ × ℝ → Fin k → lfE k := fun p i => UbaseE p i + β p • wE i
  have hUE_sm : ContDiff ℝ Cin UE := by
    refine contDiff_pi.mpr (fun i => ?_)
    exact ((contDiff_pi.mp hUbaseE_sm) i).add (hβ_sm.smul contDiff_const)
  have hUE_bot : ∀ x : ℝ, UE (x, 0) = iUE := by
    intro x
    funext i
    simp only [UE, β, hUbaseE_bot x]
    simp
  have hUE_top : ∀ x : ℝ, |x| ≤ 1 → UE (x, arch x) = U_topE x := by
    intro x hx
    funext i
    have hβ0 : β (x, arch x) = 0 := by simp [β]
    rw [show UE (x, arch x) i = UbaseE (x, arch x) i + β (x, arch x) • wE i from rfl,
      hβ0, zero_smul, add_zero]
    exact congrFun (hUbaseE_top x hx) i
  -- ======================= transporting `W` down from the top edge =======================
  let S2E : ℝ × ℝ → Fin (2 + k) → lfE k := fun p => Fin.append (pfE p) (UE p)
  have hS2E_sm : ContDiff ℝ Cin S2E := by
    refine contDiff_pi.mpr (fun j => ?_)
    induction j using Fin.addCases with
    | left j' =>
        have hfun : (fun p : ℝ × ℝ => S2E p (Fin.castAdd k j'))
            = (fun p : ℝ × ℝ => pfE p j') := by
          funext p; simp [S2E, Fin.append_left]
        rw [hfun]
        exact (contDiff_pi.mp hpfE_sm) j'
    | right j' =>
        have hfun : (fun p : ℝ × ℝ => S2E p (Fin.natAdd 2 j')) = (fun p : ℝ × ℝ => UE p j') := by
          funext p; simp [S2E, Fin.append_right]
        rw [hfun]
        exact (contDiff_pi.mp hUE_sm) j'
  have hK : lensK = {p : ℝ × ℝ | |p.1| ≤ 1 ∧ p.2 ∈ Set.Icc 0 (arch p.1)} := by
    ext p; simp only [lensK, Set.mem_Icc]
  have hindS2E : ∀ p ∈ lensK, LinearIndependent ℝ (S2E p) := fun p hp => hwE p hp
  have hedgeE : ∀ x : ℝ, |x| ≤ 1 →
      LinearIndependent ℝ (Fin.append (S2E (x, arch x)) (VE x)) := by
    intro x hx
    have hUt : UE (x, arch x) = U_topE x := hUE_top x hx
    have hSx : S2E (x, arch x) = Fin.append (pfE (x, arch x)) (U_topE x) := by
      funext j
      simp only [S2E, hUt]
    rw [hSx]
    exact hXE x hx
  obtain ⟨WE, hWE_sm, hWE_edge, hWE_ind⟩ :=
    Work.Drive.Whitney.exists_complement_fromEdge (r := 2 + k) (k := k) arch harch_sm (X' := 1)
      S2E hS2E_sm lensK hK hindS2E VE hVE_sm hedgeE
  -- ======================= transporting back to `Mdl k` =======================
  let U : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k := fun p i => T.symm (UE p i)
  let W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k := fun p i => T.symm (WE p i)
  refine ⟨U, W, ?_, ?_, ?_, ?_, ?_⟩
  · refine contDiff_pi.mpr (fun i => ?_)
    exact hTEs_sm.comp ((contDiff_pi.mp hUE_sm) i)
  · refine contDiff_pi.mpr (fun i => ?_)
    exact hTEs_sm.comp ((contDiff_pi.mp hWE_sm) i)
  · intro x
    funext i
    show T.symm (UE (x, 0) i) = iotaU k i
    rw [congrFun (hUE_bot x) i]
    simp [iUE, TE]
  · intro x hx
    funext i
    show T.symm (WE (x, arch x) i) = V x i
    rw [congrFun (hWE_edge x (abs_le.mpr hx)) i]
    simp [VE, TE]
  · intro p hp
    have hli := hWE_ind p hp
    simp only [S2E] at hli
    have hUeq : UE p = TE ∘ U p := by funext i; simp [U, TE]
    have hWeq : WE p = TE ∘ W p := by funext i; simp [W, TE]
    have hcomp : Fin.append (Fin.append (pfE p) (UE p)) (WE p)
        = TE ∘ Fin.append (Fin.append (planeFrame k dx dy p) (U p)) (W p) := by
      rw [hUeq, hWeq, show pfE p = TE ∘ planeFrame k dx dy p from rfl,
        lf_append_comp (TE : Work.Drive.Whitney.Mdl k → lfE k) (planeFrame k dx dy p) (U p),
        lf_append_comp (TE : Work.Drive.Whitney.Mdl k → lfE k)
          (Fin.append (planeFrame k dx dy p) (U p)) (W p)]
    rw [hcomp] at hli
    exact LinearIndependent.of_comp TE hli

end

end Work.Drive.PushDisc
