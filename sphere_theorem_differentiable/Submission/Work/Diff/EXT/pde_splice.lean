import Mathlib
import Submission.Work.Diff.EXT.pde_defs
import Submission.Work.Diff.EXT.contDiff_sJet_tderiv
import Submission.Work.Diff.EXT.contDiff_Aseq_Psi
import Submission.Work.Diff.EXT.jets_eq_of_t_derivs_eq
import Submission.Work.Diff.EXT.contDiffAt_of_flat_indicator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT

variable {n m : ℕ}

/-! ### Auxiliary lemmas about the spatial 2-jet and the recursion -/

/-- Congruence of the spatial 2-jet under local equality. -/
lemma sJet_congr {g h : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {z : ℝ × (Fin n → ℝ)}
    (hgh : g =ᶠ[nhds z] h) : sJet g z = sJet h z := by
  have h1 : g z = h z := hgh.eq_of_nhds
  have hcont : Tendsto (fun y : Fin n → ℝ => (z.1, y)) (nhds z.2) (nhds z) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hslice : (fun y => g (z.1, y)) =ᶠ[nhds z.2] (fun y => h (z.1, y)) :=
    hgh.comp_tendsto hcont
  have h2 : fderiv ℝ (fun y => g (z.1, y)) z.2 = fderiv ℝ (fun y => h (z.1, y)) z.2 :=
    (hslice.fderiv (𝕜 := ℝ)).eq_of_nhds
  have h3 : fderiv ℝ (fun w => fderiv ℝ (fun y => g (z.1, y)) w) z.2
      = fderiv ℝ (fun w => fderiv ℝ (fun y => h (z.1, y)) w) z.2 :=
    ((hslice.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds
  simp only [sJet, h1, h2, h3]

/-- Chain rule for a function of a tuple of functions of `(s,x)` evaluated at `(s,z.2)`. -/
lemma deriv_psi_comp {N : ℕ} {J V : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ψ : (Fin n → ℝ) × (Fin N → J) → V) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (g : Fin N → ℝ × (Fin n → ℝ) → J) (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (z : ℝ × (Fin n → ℝ)) :
    deriv (fun s : ℝ => Ψ (z.2, fun i => g i (s, z.2))) z.1
      = (fderiv ℝ Ψ (z.2, fun i => g i z)) (0, fun i => deriv (fun s => g i (s, z.2)) z.1) := by
  have h1 : HasDerivAt (fun s : ℝ => (fun i => g i (s, z.2)))
      (fun i => deriv (fun s => g i (s, z.2)) z.1) z.1 := by
    rw [hasDerivAt_pi]
    intro i
    have hd : DifferentiableAt ℝ (fun s : ℝ => g i (s, z.2)) z.1 :=
      (((hg i).differentiable (by simp)).differentiableAt).comp z.1
        (differentiableAt_id.prodMk (differentiableAt_const z.2))
    exact hd.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (z.2, fun i => g i (s, z.2)))
      (0, fun i => deriv (fun s => g i (s, z.2)) z.1) z.1 := by
    have h := (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.2 (fun i => g i (z.1, z.2))).comp_hasDerivAt z.1 h1
    simpa [Function.comp_def] using h
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ (z.2, fun i => g i z)) (z.2, fun i => g i z) :=
    ((hΨ.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h4 := h3.comp_hasDerivAt z.1 h2
  simpa [Function.comp_def] using h4.deriv

/-- Decomposition of a Pi-vector into its single-coordinate components. -/
lemma pi_single_sum {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid V] (v : ι → V) :
    (∑ i, Pi.single i (v i)) = v := by
  funext k
  simp only [Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp

/-- Decomposition of a vector whose first component is zero. -/
lemma pair_single_sum {n N : ℕ} {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (v : Fin N → J) :
    ((0 : Fin n → ℝ), v) = ∑ i, ((0 : Fin n → ℝ), Pi.single i (v i)) := by
  apply Prod.ext
  · funext k
    simp only [Prod.fst_sum, Finset.sum_apply]
    simp
  · rw [Prod.snd_sum]
    exact (pi_single_sum v).symm

/-- The defining recursion of `Psi` at `j+1`, unfolded. -/
lemma Psi_succ (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ)) (j : ℕ)
    (p : (Fin n → ℝ) × (Fin (j + 2) → SJet n m)) :
    Psi Φ (j + 1) p = ∑ i : Fin (j + 1),
      (fderiv ℝ (fun q : (Fin n → ℝ) × (Fin (j + 1) → SJet n m) => Psi Φ j q)
        (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ)) := rfl

/-- The vertical slice of a neighbourhood of `(t,x)` is a neighbourhood of `t`. -/
lemma slice_mem_nhds_of_mem_nhds {S : Set (ℝ × (Fin n → ℝ))} {z : ℝ × (Fin n → ℝ)}
    (hS : S ∈ nhds z) : {s : ℝ | (s, z.2) ∈ S} ∈ nhds z.1 := by
  have hS' : S ∈ nhds (z.1, z.2) := hS
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp (by rwa [nhds_prod_eq] at hS')
  refine mem_of_superset hU ?_
  intro s hs
  exact hUV ⟨hs, mem_of_mem_nhds hV⟩

/-- **The recursion.**  On a set `S` of `(t,x)` which is open in the time direction above each of
its points, and on which `a` solves `∂ₜa = Φ(·,Ja)`, the iterated time derivative
`Aseq Φ a j = ∂ₜ^j(Φ(·,Ja))` of the right hand side is the universal function `Psi Φ j` applied to
the spatial `2`-jets of `a, Aseq Φ a 0, …, Aseq Φ a (j-1)`. -/
theorem Aseq_eq_Psi (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    {a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {S : Set (ℝ × (Fin n → ℝ))}
    (hS : ∀ z ∈ S, S ∈ nhds z)
    (hPDE : ∀ z ∈ S, deriv (fun s => a (s, z.2)) z.1 = Φ (z.2, sJet a z))
    (hseq_diff : ∀ i : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Seq Φ a i))
    (hjet_diff : ∀ i : ℕ, ContDiff ℝ (⊤ : ℕ∞) (sJet (Seq Φ a i)))
    (hpsi_diff : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Psi Φ j))
    (hclair : ∀ (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ z : ℝ × (Fin n → ℝ), deriv (fun s => sJet g (s, z.2)) z.1 = sJet (tderiv g) z)
    (j : ℕ) : ∀ z ∈ S,
      Aseq Φ a j z = Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ a i) z) := by
  induction j with
  | zero =>
    intro z hz
    simp [Aseq, Psi, Seq]
  | succ j ih =>
    intro z hz
    rw [show Aseq Φ a (j + 1) z = deriv (fun s => Aseq Φ a j (s, z.2)) z.1 from rfl]
    have hev : (fun s : ℝ => Aseq Φ a j (s, z.2)) =ᶠ[nhds z.1]
        (fun s : ℝ => Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ a i) (s, z.2))) := by
      filter_upwards [slice_mem_nhds_of_mem_nhds (hS z hz)] with s hs
      exact ih (s, z.2) hs
    rw [hev.deriv_eq]
    rw [deriv_psi_comp (Ψ := Psi Φ j) (hΨ := hpsi_diff j)
      (g := fun i : Fin (j + 1) => sJet (Seq Φ a i)) (hg := fun i => hjet_diff i) (z := z)]
    have hdir : (fun i : Fin (j + 1) => deriv (fun s => sJet (Seq Φ a i) (s, z.2)) z.1)
        = (fun i : Fin (j + 1) => sJet (Seq Φ a (i.val + 1)) z) := by
      funext i
      rw [hclair (Seq Φ a i) (hseq_diff i) z]
      induction i using Fin.cases with
      | zero =>
        have hev0 : tderiv a =ᶠ[nhds z] Aseq Φ a 0 := by
          filter_upwards [hS z hz] with w hw
          exact hPDE w hw
        exact sJet_congr hev0
      | succ k => rfl
    rw [hdir, Psi_succ, pair_single_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc, Fin.val_succ]


/-! ### Clairaut-type facts for the spatial jet

These are the mixed-partial commutation facts needed for the recursion; they are proved here
directly from the symmetry of the second Fréchet derivative (`IsSymmSndFDerivAt`). -/

/-- The spatial slice derivative is the full Fréchet derivative composed with the inclusion of the
spatial directions. -/
lemma fderiv_comp_inr_aux {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ × V → W} {p : ℝ × V}
    (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (fun y : V => g (p.1, y)) p.2
      = (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
  have hψ : HasFDerivAt (fun y : V => (p.1, y)) (ContinuousLinearMap.inr ℝ ℝ V) p.2 :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2
  exact (hg.hasFDerivAt.comp p.2 hψ).fderiv

/-- The slice derivative map of a `C^∞` function is `C^∞`. -/
lemma contDiff_fderiv_comp_inr_aux {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ × V → W} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × V =>
      (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
  fun_prop

/-- Clairaut: the time derivative of the spatial slice derivative. -/
lemma hasDerivAt_sliceFDeriv_aux {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : ℝ × V → W} {t₀ : ℝ} {u₀ : V}
    (hΦ : ContDiffAt ℝ 2 Φ (t₀, u₀)) :
    HasDerivAt (fun t : ℝ => fderiv ℝ (fun u : V => Φ (t, u)) u₀)
      (fderiv ℝ (fun u : V => deriv (fun t : ℝ => Φ (t, u)) t₀) u₀) t₀ := by
  set P : (ℝ × V) →L[ℝ] ((ℝ × V) →L[ℝ] W) :=
    fderiv ℝ (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) with hP
  have hsymm : IsSymmSndFDerivAt ℝ Φ (t₀, u₀) := hΦ.isSymmSndFDerivAt (by norm_num)
  have hsymm_eq : ∀ v : V, P (0, v) (1, 0) = P (1, 0) (0, v) := by
    intro v
    have := hsymm.eq (0, v) (1, 0)
    simpa only [hP] using this
  have hA_cd : ContDiffAt ℝ 1 (fun p : ℝ × V => fderiv ℝ Φ p) (t₀, u₀) :=
    hΦ.fderiv_right (m := 1) (by norm_num)
  have hA_has : HasFDerivAt (fun p : ℝ × V => fderiv ℝ Φ p) P (t₀, u₀) := by
    rw [hP]
    exact (hA_cd.differentiableAt (by simp)).hasFDerivAt
  -- The composition of continuous linear maps `T ↦ T ∘ inr`, as a continuous linear map.
  let C : ((ℝ × V) →L[ℝ] W) →L[ℝ] (V →L[ℝ] W) :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] W) (ContinuousLinearMap.inr ℝ ℝ V)).comp
      (ContinuousLinearMap.compL ℝ V (ℝ × V) W)
  have hC : ∀ T : (ℝ × V) →L[ℝ] W, C T = T.comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    intro T
    simp [C, ContinuousLinearMap.compL_apply, ContinuousLinearMap.apply_apply]
  have hφ : HasFDerivAt (fun t : ℝ => (t, u₀)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
    hasFDerivAt_prodMk_left t₀ u₀
  have h1' : HasFDerivAt (fun t : ℝ => fderiv ℝ Φ (t, u₀))
      (P.comp (ContinuousLinearMap.inl ℝ ℝ V)) t₀ := hA_has.comp t₀ hφ
  have h3 := (C.hasFDerivAt.comp t₀ h1').hasDerivAt
  have e1 : (⇑C ∘ fun t : ℝ => fderiv ℝ Φ (t, u₀))
      = (fun t : ℝ => (fderiv ℝ Φ (t, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)) :=
    funext (fun t => hC _)
  have e2 : (C.comp (P.comp (ContinuousLinearMap.inl ℝ ℝ V))) 1
      = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    rw [ContinuousLinearMap.comp_apply, hC, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
  rw [e1, e2] at h3
  have hDev : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ Φ (t, u₀) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have h2ev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    exact (continuousAt_id.prodMk continuousAt_const).eventually h2ev
  have hEv : (fun t : ℝ => fderiv ℝ (fun u : V => Φ (t, u)) u₀)
      =ᶠ[𝓝 t₀] (fun t : ℝ => (fderiv ℝ Φ (t, u₀)).comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
    filter_upwards [hDev] with t ht
    exact fderiv_comp_inr_aux ht
  have hDev' : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ Φ (t₀, u) := by
    have h1ev : ∀ᶠ p in 𝓝 (t₀, u₀), ContDiffAt ℝ 1 Φ p :=
      (hΦ.of_le (by norm_num)).eventually (by simp)
    have h2ev : ∀ᶠ p in 𝓝 (t₀, u₀), DifferentiableAt ℝ Φ p :=
      h1ev.mono fun p hp => hp.differentiableAt (by simp)
    exact (continuousAt_const.prodMk continuousAt_id).eventually h2ev
  have hEv' : (fun u : V => deriv (fun t : ℝ => Φ (t, u)) t₀)
      =ᶠ[𝓝 u₀] (fun u : V => (fderiv ℝ Φ (t₀, u)) (1, 0)) := by
    filter_upwards [hDev'] with u hu
    have hφ' : HasFDerivAt (fun t : ℝ => (t, u)) (ContinuousLinearMap.inl ℝ ℝ V) t₀ :=
      hasFDerivAt_prodMk_left t₀ u
    have h := (hu.hasFDerivAt.comp t₀ hφ').hasDerivAt
    have h' := h.deriv
    simp only [Function.comp_def] at h'
    rw [h']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hR : HasFDerivAt (fun u : V => (fderiv ℝ Φ (t₀, u)) (1, 0))
      ((ContinuousLinearMap.apply ℝ W (1, 0)).comp
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V))) u₀ := by
    have hψ : HasFDerivAt (fun u : V => (t₀, u)) (ContinuousLinearMap.inr ℝ ℝ V) u₀ :=
      hasFDerivAt_prodMk_right t₀ u₀
    have h1'' : HasFDerivAt (fun u : V => fderiv ℝ Φ (t₀, u))
        (P.comp (ContinuousLinearMap.inr ℝ ℝ V)) u₀ := hA_has.comp u₀ hψ
    have h2 := (ContinuousLinearMap.apply ℝ W (1, 0)).hasFDerivAt.comp u₀ h1''
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2
  have hval : fderiv ℝ (fun u : V => deriv (fun t : ℝ => Φ (t, u)) t₀) u₀
      = (P (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
    rw [hEv'.fderiv_eq, hR.fderiv]
    ext v
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply] using hsymm_eq v
  rw [hval]
  exact h3.congr_of_eventuallyEq hEv

/-- **Clairaut for the spatial `2`-jet.** -/
lemma deriv_sJet_aux {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∀ z : ℝ × (Fin n → ℝ), deriv (fun s => sJet g (s, z.2)) z.1 = sJet (tderiv g) z := by
  intro z
  obtain ⟨t, x⟩ := z
  set A' : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    fderiv ℝ (fun y : Fin n → ℝ => tderiv g (t, y)) x with hA'def
  set B' : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
    fderiv ℝ (fun w : Fin n → ℝ => fderiv ℝ (fun y : Fin n → ℝ => tderiv g (t, y)) w) x
    with hB'def
  set H : ℝ × (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
    fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) with hHdef
  have hH_smooth : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHdef]
    exact contDiff_fderiv_comp_inr_aux hg
  have hH2 : ContDiffAt ℝ 2 H (t, x) := (hH_smooth.contDiffAt).of_le (by norm_num)
  have hHpt : ∀ (s : ℝ) (w : Fin n → ℝ), H (s, w) = fderiv ℝ (fun y => g (s, y)) w := by
    intro s w
    rw [hHdef]
    exact (fderiv_comp_inr_aux ((hg.contDiffAt).differentiableAt (by simp))).symm
  have hG : HasDerivAt (fun s : ℝ => g (s, x)) (tderiv g (t, x)) t := by
    have hslice : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => g (s, x)) t :=
      ContDiffAt.comp t (hg.contDiffAt) (contDiffAt_id.prodMk contDiffAt_const)
    exact (hslice.differentiableAt (by simp)).hasFDerivAt.hasDerivAt
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y => g (s, y)) x) A' t :=
    hasDerivAt_sliceFDeriv_aux ((hg.contDiffAt).of_le (by norm_num))
  have hHw : ∀ w : Fin n → ℝ,
      deriv (fun s : ℝ => H (s, w)) t = fderiv ℝ (fun y : Fin n → ℝ => tderiv g (t, y)) w := by
    intro w
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y => g (s, y)) w)
        (fderiv ℝ (fun y : Fin n → ℝ => deriv (fun s : ℝ => g (s, y)) t) w) t :=
      hasDerivAt_sliceFDeriv_aux ((hg.contDiffAt).of_le (by norm_num))
    have h3 : HasDerivAt (fun s : ℝ => H (s, w))
        (fderiv ℝ (fun y : Fin n → ℝ => deriv (fun s : ℝ => g (s, y)) t) w) t :=
      h1.congr_of_eventuallyEq (Eventually.of_forall (fun s => hHpt s w))
    exact h3.deriv
  have hB : HasDerivAt (fun s : ℝ => fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x) B' t := by
    have h0 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun w => H (s, w)) x)
        (fderiv ℝ (fun w : Fin n → ℝ => deriv (fun s : ℝ => H (s, w)) t) x) t :=
      hasDerivAt_sliceFDeriv_aux hH2
    have hval : fderiv ℝ (fun w : Fin n → ℝ => deriv (fun s : ℝ => H (s, w)) t) x = B' :=
      EventuallyEq.fderiv_eq (Eventually.of_forall (fun w => hHw w))
    have hfun : (fun s : ℝ => fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)
        =ᶠ[𝓝 t] (fun s : ℝ => fderiv ℝ (fun w => H (s, w)) x) :=
      Eventually.of_forall (fun s => by
        show fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x
          = fderiv ℝ (fun w => H (s, w)) x
        rw [show (fun w : Fin n → ℝ => H (s, w))
            = (fun w => fderiv ℝ (fun y => g (s, y)) w) from funext (fun w => hHpt s w)])
    have h1 := h0.congr_of_eventuallyEq hfun
    rw [hval] at h1
    exact h1
  have hprod : HasDerivAt
      (fun s : ℝ => (g (s, x), (fderiv ℝ (fun y => g (s, y)) x,
        fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)))
      (tderiv g (t, x), (A', B')) t :=
    hG.prodMk (hA.prodMk hB)
  have hjet_eq : (fun s : ℝ => sJet g (s, x)) = fun s =>
      (g (s, x), (fderiv ℝ (fun y => g (s, y)) x,
        fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)) := by
    funext s
    rfl
  have hderiv :=
    (hprod.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun hjet_eq s))).deriv
  rw [hderiv]
  simp only [hA'def, hB'def, sJet]

/-! ### From the recursion on the half-space to the hyperplane -/

/-- The `n+1`-th iterated derivative is the derivative of the `n`-th one. -/
lemma deriv_iteratedDeriv (n : ℕ) (f : ℝ → (Fin m → ℝ)) (s : ℝ) :
    deriv (fun s' => iteratedDeriv n f s') s = iteratedDeriv (n + 1) f s := by
  rw [iteratedDeriv_succ]

/-- `Aseq Φ a j` is the `(j+1)`-st time derivative of `a` on a set where `a` solves the equation. -/
lemma Aseq_eq_iteratedDeriv (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    {a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {S : Set (ℝ × (Fin n → ℝ))}
    (hS : ∀ z ∈ S, S ∈ nhds z)
    (hPDE : ∀ z ∈ S, deriv (fun s => a (s, z.2)) z.1 = Φ (z.2, sJet a z)) (j : ℕ) :
    ∀ z ∈ S, Aseq Φ a j z = iteratedDeriv (j + 1) (fun s => a (s, z.2)) z.1 := by
  induction j with
  | zero =>
    intro z hz
    simp only [Aseq]
    rw [← hPDE z hz]
    simp [iteratedDeriv_succ', iteratedDeriv_zero]
  | succ j ih =>
    intro z hz
    rw [show Aseq Φ a (j + 1) z = deriv (fun s => Aseq Φ a j (s, z.2)) z.1 from rfl]
    have hev : (fun s : ℝ => Aseq Φ a j (s, z.2))
        =ᶠ[nhds z.1] (fun s : ℝ => iteratedDeriv (j + 1) (fun s' => a (s', z.2)) s) := by
      filter_upwards [slice_mem_nhds_of_mem_nhds (hS z hz)] with s hs
      exact ih (s, z.2) hs
    rw [hev.deriv_eq, deriv_iteratedDeriv]

/-- The recursion extends to the hyperplane along a curve approaching it inside `S`. -/
lemma Aseq_eq_Psi_at_of_curve (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    {a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {S : Set (ℝ × (Fin n → ℝ))} {T : ℝ}
    {x : Fin n → ℝ}
    (hrec : ∀ j : ℕ, ∀ z ∈ S,
      Aseq Φ a j z = Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ a i) z))
    (hA_cont : ∀ j : ℕ, Continuous (Aseq Φ a j))
    (hPsi_cont : ∀ j : ℕ, Continuous (fun z : ℝ × (Fin n → ℝ) =>
      Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ a i) z)))
    (c : ℝ → ℝ) (hc : Tendsto c (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T))
    (hcmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (c ε, x) ∈ S)
    (j : ℕ) :
    Aseq Φ a j (T, x) = Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ a i) (T, x)) := by
  have hcur : Tendsto (fun ε : ℝ => (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (T, x)) :=
    hc.prodMk_nhds tendsto_const_nhds
  have h1 : Tendsto (fun ε : ℝ => Aseq Φ a j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (Aseq Φ a j (T, x))) := (hA_cont j).continuousAt.tendsto.comp hcur
  have h2 : Tendsto (fun ε : ℝ => Aseq Φ a j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ a i) (T, x)))) := by
    refine ((hPsi_cont j).continuousAt.tendsto.comp hcur).congr' ?_
    filter_upwards [hcmem] with ε hε
    exact (hrec j (c ε, x) hε).symm
  exact tendsto_nhds_unique h1 h2

/-- Congruence of the spatial 2-jet on the hyperplane under agreement of the slice functions. -/
lemma sJet_slice_congr {T : ℝ} {x : Fin n → ℝ}
    {g h : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (hgh : (fun y => g (T, y)) =ᶠ[nhds x] (fun y => h (T, y))) :
    sJet g (T, x) = sJet h (T, x) := by
  have h1 : g (T, x) = h (T, x) := hgh.eq_of_nhds
  have h2 : fderiv ℝ (fun y => g (T, y)) x = fderiv ℝ (fun y => h (T, y)) x :=
    (hgh.fderiv (𝕜 := ℝ)).eq_of_nhds
  have h3 : fderiv ℝ (fun w => fderiv ℝ (fun y => g (T, y)) w) x
      = fderiv ℝ (fun w => fderiv ℝ (fun y => h (T, y)) w) x :=
    ((hgh.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds
  simp only [sJet, h1, h2, h3]

/-- On a common open set the slice functions agree, hence so do the spatial 2-jets. -/
lemma sJet_slice_congr_of_open {T : ℝ} {U : Set (Fin n → ℝ)} (hUo : IsOpen U)
    {x : Fin n → ℝ} (hx : x ∈ U) {g h : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (hgh : ∀ y ∈ U, g (T, y) = h (T, y)) :
    sJet g (T, x) = sJet h (T, x) :=
  sJet_slice_congr (by
    filter_upwards [hUo.mem_nhds hx] with y hy
    exact hgh y hy)

/-- Agreement of the `Aseq`-sequences at the hyperplane over a common open set. -/
lemma Aseq_agree (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ)) {T : ℝ}
    {u v : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (hu_T : ∀ (j : ℕ) (x : Fin n → ℝ),
      Aseq Φ u j (T, x) = Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ u i) (T, x)))
    (hv_T : ∀ (j : ℕ) (x : Fin n → ℝ),
      Aseq Φ v j (T, x) = Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ v i) (T, x)))
    {U : Set (Fin n → ℝ)} (hUo : IsOpen U) (hU : ∀ x ∈ U, sJet u (T, x) = sJet v (T, x)) :
    ∀ x ∈ U, ∀ j : ℕ, Aseq Φ u j (T, x) = Aseq Φ v j (T, x) := by
  have hAC : ∀ j : ℕ, ∀ x ∈ U, Aseq Φ u j (T, x) = Aseq Φ v j (T, x) := by
    intro j
    refine Nat.strong_induction_on (p := fun j => ∀ x ∈ U,
      Aseq Φ u j (T, x) = Aseq Φ v j (T, x)) j ?_
    intro j ih x hx
    match j with
    | 0 =>
      simp only [Aseq]
      rw [hU x hx]
    | (j' + 1) =>
      rw [hu_T (j' + 1) x, hv_T (j' + 1) x]
      have hjet : (fun i : Fin (j' + 2) => sJet (Seq Φ u i) (T, x))
          = (fun i : Fin (j' + 2) => sJet (Seq Φ v i) (T, x)) := by
        funext i
        induction i using Fin.cases with
        | zero => exact hU x hx
        | succ k =>
          refine sJet_slice_congr_of_open hUo hx (fun y hy => ?_)
          exact ih k.val k.isLt y hy
      rw [hjet]
  intro x hx j
  exact hAC j x hx

end Work.Diff.EXT

namespace Work.Diff.EXT

variable {n m : ℕ}

/-- `iteratedFDeriv ℝ 0` agreement gives pointwise agreement of the functions. -/
lemma eq_of_iteratedFDeriv_zero {T : ℝ} {x₀ : Fin n → ℝ}
    {u v : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (hjets : ∀ᶠ x in nhds x₀, ∀ k : ℕ, iteratedFDeriv ℝ k (fun y => u (T, y)) x
      = iteratedFDeriv ℝ k (fun y => v (T, y)) x) :
    (fun y => u (T, y)) =ᶠ[nhds x₀] (fun y => v (T, y)) := by
  filter_upwards [hjets] with x hx
  have h := congrArg (continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) (Fin m → ℝ)) (hx 0)
  simpa [iteratedFDeriv_zero_eq_comp] using h

/-- From a local equality of the slice functions we get an open set on which they agree. -/
lemma exists_open_slice_eq {T : ℝ} {x₀ : Fin n → ℝ}
    {u v : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (h : (fun y => u (T, y)) =ᶠ[nhds x₀] (fun y => v (T, y))) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, u (T, x) = v (T, x) := by
  have hmem : {x : Fin n → ℝ | u (T, x) = v (T, x)} ∈ nhds x₀ := h
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hmem
  exact ⟨U, hUo, hxU, fun x hx => hUsub hx⟩

/-- The `(j+1)`-st time derivative at the hyperplane, computed as the limit along a curve inside
the half-space where the equation holds. -/
lemma iteratedDeriv_eq_Aseq_at_hyperplane (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    {w : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {S : Set (ℝ × (Fin n → ℝ))} {T : ℝ}
    {x : Fin n → ℝ} {j : ℕ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hrec : ∀ z ∈ S, Aseq Φ w j z = iteratedDeriv (j + 1) (fun s => w (s, z.2)) z.1)
    (hA_cont : Continuous (Aseq Φ w j))
    (c : ℝ → ℝ) (hc : Tendsto c (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T))
    (hcmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (c ε, x) ∈ S) :
    iteratedDeriv (j + 1) (fun s => w (s, x)) T = Aseq Φ w j (T, x) := by
  have hcw : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => w (t, x)) :=
    hw.comp (contDiff_id.prodMk contDiff_const)
  have hcont1 : Continuous (iteratedDeriv (j + 1) (fun s => w (s, x))) :=
    ContDiff.continuous_iteratedDeriv (j + 1) hcw
      (WithTop.coe_le_coe.mpr (le_top : ((j + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have ht1 : Tendsto (fun ε : ℝ => iteratedDeriv (j + 1) (fun s => w (s, x)) (c ε))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (iteratedDeriv (j + 1) (fun s => w (s, x)) T)) :=
    hcont1.continuousAt.tendsto.comp hc
  have ht2 : Tendsto (fun ε : ℝ => iteratedDeriv (j + 1) (fun s => w (s, x)) (c ε))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (Aseq Φ w j (T, x))) := by
    have h3 : Tendsto (fun ε : ℝ => Aseq Φ w j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (Aseq Φ w j (T, x))) :=
      hA_cont.continuousAt.tendsto.comp (hc.prodMk_nhds tendsto_const_nhds)
    refine h3.congr' ?_
    filter_upwards [hcmem] with ε hε
    exact hrec (c ε, x) hε
  exact tendsto_nhds_unique ht1 ht2

/-- The time Taylor coefficients of two functions agree on the hyperplane, given the agreement of
the `Aseq`-sequences and the one-sided limits. -/
lemma gamma_agree (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ)) {T : ℝ}
    {u v : ℝ × (Fin n → ℝ) → (Fin m → ℝ)} {U : Set (Fin n → ℝ)}
    (hUV : ∀ x ∈ U, u (T, x) = v (T, x))
    (hAC : ∀ x ∈ U, ∀ j : ℕ, Aseq Φ u j (T, x) = Aseq Φ v j (T, x))
    (hkey_u : ∀ x ∈ U, ∀ j : ℕ, iteratedDeriv (j + 1) (fun s => u (s, x)) T
      = Aseq Φ u j (T, x))
    (hkey_v : ∀ x ∈ U, ∀ j : ℕ, iteratedDeriv (j + 1) (fun s => v (s, x)) T
      = Aseq Φ v j (T, x)) :
    ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s => u (s, x)) T
      = iteratedDeriv i (fun s => v (s, x)) T := by
  intro x hx i
  rcases i with _ | j
  · simpa using hUV x hx
  · rw [hkey_u x hx j, hkey_v x hx j, hAC x hx j]

/-- Smoothness of the spatial 2-jet of `Seq Φ a i`. -/
lemma contDiff_sJet_seq (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (i : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sJet (Seq Φ a i)) :=
  (contDiff_sJet_tderiv (Seq Φ a i) ((contDiff_Aseq_Psi Φ hΦ a ha).2.1 i)).1

/-- Smoothness of the composed `Psi` expression. -/
lemma contDiff_psi_composite (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) =>
      Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ a i) z)) := by
  refine ((contDiff_Aseq_Psi Φ hΦ a ha).2.2 j).comp ?_
  refine ContDiff.prodMk contDiff_snd ?_
  exact contDiff_pi.mpr (fun i => contDiff_sJet_seq Φ hΦ ha i)

/-- **Splicing two solutions of a quasilinear parabolic system at a hyperplane.**  For
`u : ℝ × ℝⁿ → ℝᵐ`, write `J u t x = (u t x, ∂ₓu, ∂ₓ²u)` for its *spatial* `2`-jet at `(t,x)`, of type
`(ℝᵐ) × (ℝⁿ →L ℝᵐ) × (ℝⁿ →L ℝⁿ →L ℝᵐ)`.  If `u` solves `∂ₜ u = Φ(·, J u)` on `{t < T}` and `v`
solves the same equation on `{t > T}`, and if the *spatial* jets of `u` and `v` agree to all orders at
`(T, x)` for every `x` near `x₀`, then the function obtained by splicing `u` (for `t ≤ T`) with `v`
(for `t > T`) is `C^∞` at `(T, x₀)`.  (A neighbourhood statement, so agreement near `x₀` — not only
at `x₀` — is needed.)  `(⊤ : ℕ∞)` means smoothness, i.e. the level usually written `∞`; a literal
`⊤` in that position would mean `ω` (analytic). -/
theorem pde_splice
    {n m : ℕ} {T : ℝ} {x₀ : Fin n → ℝ}
    (Φ : (Fin n → ℝ) ×
        ((Fin m → ℝ) × ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) ×
          ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) → (Fin m → ℝ))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {u v : ℝ × (Fin n → ℝ) → (Fin m → ℝ)}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (huS : ∀ t, t < T → ∀ x,
      deriv (fun s => u (s, x)) t = Φ (x, (u (t, x), fderiv ℝ (fun y => u (t, y)) x,
        fderiv ℝ (fun y => fderiv ℝ (fun z => u (t, z)) y) x)))
    (hvS : ∀ t, T < t → ∀ x,
      deriv (fun s => v (s, x)) t = Φ (x, (v (t, x), fderiv ℝ (fun y => v (t, y)) x,
        fderiv ℝ (fun y => fderiv ℝ (fun z => v (t, z)) y) x)))
    (hjets : ∀ᶠ x in nhds x₀, ∀ k : ℕ, iteratedFDeriv ℝ k (fun y => u (T, y)) x
              = iteratedFDeriv ℝ k (fun y => v (T, y)) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => if p.1 ≤ T then u p else v p) (T, x₀) := by
  have hclair : ∀ (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ z : ℝ × (Fin n → ℝ), deriv (fun s => sJet g (s, z.2)) z.1 = sJet (tderiv g) z :=
    fun g hg => deriv_sJet_aux g hg
  -- the two half-spaces
  have hSu_open : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < T},
      ({z : ℝ × (Fin n → ℝ) | z.1 < T} ∈ nhds z) := fun z hz =>
    (isOpen_lt continuous_fst continuous_const).mem_nhds hz
  have hSv_open : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | T < z.1},
      ({z : ℝ × (Fin n → ℝ) | T < z.1} ∈ nhds z) := fun z hz =>
    (isOpen_lt continuous_const continuous_fst).mem_nhds hz
  have hPDE_u : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < T},
      deriv (fun s => u (s, z.2)) z.1 = Φ (z.2, sJet u z) := fun z hz => huS z.1 hz z.2
  have hPDE_v : ∀ z ∈ {z : ℝ × (Fin n → ℝ) | T < z.1},
      deriv (fun s => v (s, z.2)) z.1 = Φ (z.2, sJet v z) := fun z hz => hvS z.1 hz z.2
  -- smoothness data
  have hAs_u := contDiff_Aseq_Psi Φ hΦ u hu
  have hAs_v := contDiff_Aseq_Psi Φ hΦ v hv
  have hjet_u : ∀ i : ℕ, ContDiff ℝ (⊤ : ℕ∞) (sJet (Seq Φ u i)) := fun i =>
    contDiff_sJet_seq Φ hΦ hu i
  have hjet_v : ∀ i : ℕ, ContDiff ℝ (⊤ : ℕ∞) (sJet (Seq Φ v i)) := fun i =>
    contDiff_sJet_seq Φ hΦ hv i
  have hpsi_u : ∀ j : ℕ, Continuous (fun z : ℝ × (Fin n → ℝ) =>
      Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ u i) z)) := fun j =>
    (contDiff_psi_composite Φ hΦ hu j).continuous
  have hpsi_v : ∀ j : ℕ, Continuous (fun z : ℝ × (Fin n → ℝ) =>
      Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ v i) z)) := fun j =>
    (contDiff_psi_composite Φ hΦ hv j).continuous
  -- the recursion on the two half-spaces
  have hrec_u : ∀ j : ℕ, ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < T},
      Aseq Φ u j z = Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ u i) z) := fun j =>
    Aseq_eq_Psi Φ hSu_open hPDE_u hAs_u.2.1 hjet_u hAs_u.2.2 hclair j
  have hrec_v : ∀ j : ℕ, ∀ z ∈ {z : ℝ × (Fin n → ℝ) | T < z.1},
      Aseq Φ v j z = Psi Φ j (z.2, fun i : Fin (j + 1) => sJet (Seq Φ v i) z) := fun j =>
    Aseq_eq_Psi Φ hSv_open hPDE_v hAs_v.2.1 hjet_v hAs_v.2.2 hclair j
  have hder_u : ∀ j : ℕ, ∀ z ∈ {z : ℝ × (Fin n → ℝ) | z.1 < T},
      Aseq Φ u j z = iteratedDeriv (j + 1) (fun s => u (s, z.2)) z.1 := fun j =>
    Aseq_eq_iteratedDeriv Φ hSu_open hPDE_u j
  have hder_v : ∀ j : ℕ, ∀ z ∈ {z : ℝ × (Fin n → ℝ) | T < z.1},
      Aseq Φ v j z = iteratedDeriv (j + 1) (fun s => v (s, z.2)) z.1 := fun j =>
    Aseq_eq_iteratedDeriv Φ hSv_open hPDE_v j
  -- curves approaching the hyperplane from inside each half-space
  have hcu : Tendsto (fun ε : ℝ => T - ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) := by
    have h1 : Tendsto (fun _ : ℝ => T) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
      tendsto_id.mono_left (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from
        nhdsWithin_le_nhds)
    simpa using h1.sub h2
  have hcv : Tendsto (fun ε : ℝ => T + ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) := by
    have h1 : Tendsto (fun _ : ℝ => T) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
      tendsto_id.mono_left (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) from
        nhdsWithin_le_nhds)
    simpa using h1.add h2
  have hmemu : ∀ x : Fin n → ℝ,
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (T - ε, x) ∈ {z : ℝ × (Fin n → ℝ) | z.1 < T} := by
    intro x
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using sub_lt_self T hε
  have hmemv : ∀ x : Fin n → ℝ,
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (T + ε, x) ∈ {z : ℝ × (Fin n → ℝ) | T < z.1} := by
    intro x
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_add_of_pos_right T hε
  -- the recursion at the hyperplane
  have hT_u : ∀ (j : ℕ) (x : Fin n → ℝ),
      Aseq Φ u j (T, x) = Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ u i) (T, x)) :=
    fun j x => Aseq_eq_Psi_at_of_curve Φ hrec_u (fun j => (hAs_u.1 j).continuous) hpsi_u
      (fun ε => T - ε) hcu (hmemu x) j
  have hT_v : ∀ (j : ℕ) (x : Fin n → ℝ),
      Aseq Φ v j (T, x) = Psi Φ j (x, fun i : Fin (j + 1) => sJet (Seq Φ v i) (T, x)) :=
    fun j x => Aseq_eq_Psi_at_of_curve Φ hrec_v (fun j => (hAs_v.1 j).continuous) hpsi_v
      (fun ε => T + ε) hcv (hmemv x) j
  -- the one-sided limits of the time derivatives
  have hkey_u : ∀ x : Fin n → ℝ, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s => u (s, x)) T = Aseq Φ u j (T, x) := fun x j =>
    iteratedDeriv_eq_Aseq_at_hyperplane Φ hu (fun z hz => hder_u j z hz)
      (hAs_u.1 j).continuous (fun ε => T - ε) hcu (hmemu x)
  have hkey_v : ∀ x : Fin n → ℝ, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s => v (s, x)) T = Aseq Φ v j (T, x) := fun x j =>
    iteratedDeriv_eq_Aseq_at_hyperplane Φ hv (fun z hz => hder_v j z hz)
      (hAs_v.1 j).continuous (fun ε => T + ε) hcv (hmemv x)
  -- the slice functions agree near x₀
  have hslice : (fun y => u (T, y)) =ᶠ[nhds x₀] (fun y => v (T, y)) :=
    eq_of_iteratedFDeriv_zero hjets
  obtain ⟨U, hUo, hxU, hUslice⟩ := exists_open_slice_eq hslice
  have hUsJet : ∀ x ∈ U, sJet u (T, x) = sJet v (T, x) := fun x hx =>
    sJet_slice_congr_of_open hUo hx hUslice
  -- the `Aseq`-comparison and the agreement of the time Taylor coefficients
  have hAC := Aseq_agree Φ hT_u hT_v hUo hUsJet
  have hgamma : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s => u (s, x)) T
      = iteratedDeriv i (fun s => v (s, x)) T := fun x hx i =>
    gamma_agree Φ (fun y hy => hUslice y hy) (fun y hy => hAC y hy)
      (fun y hy j => hkey_u y j) (fun y hy j => hkey_v y j) x hx i
  -- the full jets agree on `U`
  have hjetsU : ∀ x ∈ U, ∀ k : ℕ,
      iteratedFDeriv ℝ k u (T, x) = iteratedFDeriv ℝ k v (T, x) :=
    jets_eq_of_t_derivs_eq hUo hu hv hgamma
  have hjets' : ∀ᶠ x in nhds x₀, ∀ k : ℕ,
      iteratedFDeriv ℝ k u (T, x) = iteratedFDeriv ℝ k v (T, x) := by
    filter_upwards [hUo.mem_nhds hxU] with x hx
    exact hjetsU x hx
  -- the difference `u - v` is flat on the hyperplane near `x₀`
  have hflat : ∀ᶠ x in nhds x₀, ∀ k : ℕ,
      iteratedFDeriv ℝ k (fun p : ℝ × (Fin n → ℝ) => u p - v p) (T, x) = 0 := by
    filter_upwards [hUo.mem_nhds hxU] with x hx
    intro k
    have h1 : ContDiffAt ℝ (↑k) u (T, x) :=
      (hu.contDiffAt).of_le (WithTop.coe_le_coe.mpr (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
    have h2 : ContDiffAt ℝ (↑k) v (T, x) :=
      (hv.contDiffAt).of_le (WithTop.coe_le_coe.mpr (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
    rw [show (fun p : ℝ × (Fin n → ℝ) => u p - v p) = u - v from rfl,
      iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := (T, x)) h1 h2, hjetsU x hx k, sub_self]
  have hδ : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p - v p) (T, x₀) :=
    (hu.sub hv).contDiffAt
  have hind := contDiffAt_of_flat_indicator (x₀ := x₀) (T := T) hδ hflat
  have hEq : (fun p : ℝ × (Fin n → ℝ) => if p.1 ≤ T then u p else v p)
      = fun p => u p - (if p.1 ≤ T then (0 : Fin m → ℝ) else u p - v p) := by
    funext p
    by_cases hp : p.1 ≤ T <;> simp [hp]
  rw [hEq]
  exact (hu.contDiffAt).sub hind

end Work.Diff.EXT
