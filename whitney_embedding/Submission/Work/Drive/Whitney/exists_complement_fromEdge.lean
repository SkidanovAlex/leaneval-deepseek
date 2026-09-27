import Mathlib
import Submission.Work.Drive.Whitney.smooth_kernelProjection_twoParam
import Submission.Work.Drive.Whitney.bumpCompactOfOpen
import Submission.Work.Drive.Whitney.projFamilyOfVanishingLambda
import Submission.Work.Drive.Whitney.katoStepBijective
import Submission.Work.Drive.Whitney.appendSpanCongr
import Submission.Work.Drive.Whitney.appendMapInjective
import Submission.Work.Drive.Whitney.meshStepBound

namespace Work.Drive.Whitney

open scoped ContDiff Topology
open Set Filter

private abbrev Cin : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The Kato step `Q * P + (1 - Q) * (1 - P)`. -/
noncomputable def katoMap {m : ℕ}
    (P Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := Q * P + (1 - Q) * (1 - P)

theorem katoMap_self {m : ℕ} {P : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hP : P * P = P) : katoMap P P = 1 := by
  rw [katoMap]
  have h : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP]
    abel
  rw [hP, h, add_sub_cancel]

theorem exists_complement_fromEdge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {r k : ℕ} (c : ℝ → ℝ) (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) {X' : ℝ}
    (S : ℝ × ℝ → Fin r → F) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (K : Set (ℝ × ℝ)) (hK : K = {p : ℝ × ℝ | |p.1| ≤ X' ∧ p.2 ∈ Set.Icc 0 (c p.1)})
    (hindS : ∀ p ∈ K, LinearIndependent ℝ (S p))
    (V : ℝ → Fin k → F) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hedge : ∀ x : ℝ, |x| ≤ X' → LinearIndependent ℝ (Fin.append (S (x, c x)) (V x))) :
    ∃ W : ℝ × ℝ → Fin k → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      (∀ x : ℝ, |x| ≤ X' → W (x, c x) = V x) ∧
      ∀ p ∈ K, LinearIndependent ℝ (Fin.append (S p) (W p)) := by
  classical
  by_cases hXlt : X' < 0
  · refine ⟨fun _ _ => 0, contDiff_const, ?_, ?_⟩
    · intro x hx
      exact absurd hx (not_le.mpr (lt_of_lt_of_le hXlt (abs_nonneg x)))
    · intro p hp
      rw [hK] at hp
      exact absurd hp.1 (not_le.mpr (lt_of_lt_of_le hXlt (abs_nonneg p.1)))
  have hX0 : 0 ≤ X' := le_of_not_gt hXlt
  -- ## 1. transport to the Euclidean model
  set m : ℕ := Module.finrank ℝ F with hm
  let e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) := (stdOrthonormalBasis ℝ F).repr
  have he : ContDiff ℝ Cin (fun v : F => e v) := LinearIsometryEquiv.contDiff e
  have heker : (e.toLinearEquiv : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun a b hab => e.injective hab)
  set S' : ℝ × ℝ → Fin r → EuclideanSpace ℝ (Fin m) := fun p i => e (S p i) with hS'def
  set V' : ℝ → Fin k → EuclideanSpace ℝ (Fin m) := fun x j => e (V x j) with hV'def
  have hS' : ∀ i, ContDiff ℝ Cin (fun p : ℝ × ℝ => S' p i) := by
    intro i
    have h1 : ContDiff ℝ Cin (fun p : ℝ × ℝ => S p i) := (contDiff_pi.mp hS) i
    have h2 : ContDiff ℝ Cin (fun p : ℝ × ℝ => e (S p i)) := he.comp h1
    simpa only [S'] using h2
  have hV' : ∀ j, ContDiff ℝ Cin (fun x : ℝ => V' x j) := by
    intro j
    have h1 : ContDiff ℝ Cin (fun x : ℝ => V x j) := (contDiff_pi.mp hV) j
    have h2 : ContDiff ℝ Cin (fun x : ℝ => e (V x j)) := he.comp h1
    simpa only [V'] using h2
  -- ## 2. the compact set `Z = K ∪ E` and the frame family there
  obtain ⟨M₀, hM₀⟩ := IsCompact.exists_bound_of_continuousOn
    (s := Set.Icc (-X') X') isCompact_Icc (hc.continuous.continuousOn)
  set M : ℝ := max M₀ 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMle : ∀ x ∈ Set.Icc (-X') X', |c x| ≤ M := by
    intro x hx
    have h : ‖c x‖ ≤ M₀ := hM₀ x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hKcomp : IsCompact K := by
    rw [hK]
    refine IsCompact.of_isClosed_subset
      ((isCompact_Icc (a := -X') (b := X')).prod (isCompact_Icc (a := -M) (b := M))) ?_ ?_
    · have h1 : IsClosed {p : ℝ × ℝ | |p.1| ≤ X'} := by
        have heq : {p : ℝ × ℝ | |p.1| ≤ X'}
            = (fun p : ℝ × ℝ => |p.1|) ⁻¹' Set.Icc (-X') X' := by
          ext p
          constructor
          · intro h
            rw [Set.mem_preimage, Set.mem_Icc]
            exact ⟨by linarith [abs_nonneg p.1, hX0], h⟩
          · intro h
            rw [Set.mem_preimage, Set.mem_Icc] at h
            exact h.2
        rw [heq]
        exact isClosed_Icc.preimage (continuous_abs.comp continuous_fst)
      have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
      have h3 : IsClosed {p : ℝ × ℝ | p.2 ≤ c p.1} :=
        isClosed_le continuous_snd (hc.continuous.comp continuous_fst)
      have h4 : {p : ℝ × ℝ | |p.1| ≤ X' ∧ p.2 ∈ Set.Icc 0 (c p.1)}
          = {p : ℝ × ℝ | |p.1| ≤ X'} ∩ {p : ℝ × ℝ | 0 ≤ p.2}
            ∩ {p : ℝ × ℝ | p.2 ≤ c p.1} := by
        ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc]; tauto
      rw [h4]
      exact (h1.inter h2).inter h3
    · intro p hp
      simp only [Set.mem_setOf_eq] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      have h1' : -X' ≤ p.1 ∧ p.1 ≤ X' := abs_le.mp h1
      have hcx : |c p.1| ≤ M := hMle p.1 (by rw [Set.mem_Icc]; exact h1')
      obtain ⟨hcx1, hcx2⟩ := abs_le.mp hcx
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc]; exact h1'
      · rw [Set.mem_Icc]
        exact ⟨le_trans (neg_nonpos.mpr hMpos.le) h2, le_trans h3 hcx2⟩
  set E : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| ≤ X' ∧ p.2 = c p.1} with hEdef
  have hEcomp : IsCompact E := by
    have heq : E = (fun x : ℝ => (x, c x)) '' Set.Icc (-X') X' := by
      ext p; constructor
      · intro hp
        rw [hEdef] at hp
        exact ⟨p.1, by rw [Set.mem_Icc]; exact abs_le.mp hp.1, by
          show (p.1, c p.1) = p
          rw [← hp.2]⟩
      · rintro ⟨x, hx, rfl⟩
        rw [hEdef]
        exact ⟨by rw [abs_le]; exact hx, rfl⟩
    rw [heq]
    exact isCompact_Icc.image (continuous_id.prodMk hc.continuous)
  set Z : Set (ℝ × ℝ) := K ∪ E with hZdef
  have hZcomp : IsCompact Z := hKcomp.union hEcomp
  have hinter : ∀ p ∈ K, p.2 ≤ c p.1 := by
    intro p hp; rw [hK] at hp; exact (Set.mem_Icc.mp hp.2).2
  have hindK : ∀ p ∈ K, 0 ≤ p.2 := by
    intro p hp; rw [hK] at hp; exact (Set.mem_Icc.mp hp.2).1
  have hZind : ∀ p ∈ Z, LinearIndependent ℝ (S p) := by
    intro p hp
    rw [hZdef] at hp
    rcases hp with hp | hp
    · exact hindS p hp
    · rw [hEdef] at hp
      obtain ⟨h1, h2⟩ := hp
      have h3 : LinearIndependent ℝ (Fin.append (S (p.1, c p.1)) (V p.1)) := hedge p.1 h1
      have h4 : p = (p.1, c p.1) := by ext <;> simp [h2]
      rw [h4]
      have h5 : LinearIndependent ℝ
          (fun i : Fin r => Fin.append (S (p.1, c p.1)) (V p.1) (Fin.castAdd k i)) :=
        h3.comp (Fin.castAdd k) (Fin.castAdd_injective r k)
      simpa [Fin.append_left] using h5
  have hZind' : ∀ p ∈ Z, LinearIndependent ℝ (S' p) := by
    intro p hp
    have h1 : LinearIndependent ℝ (S p) := hZind p hp
    have h2 : LinearIndependent ℝ
        (fun i : Fin r => (e.toLinearEquiv : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (S p i)) :=
      (LinearMap.linearIndependent_iff
        (e.toLinearEquiv : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) heker).mpr h1
    have h3 : (fun i : Fin r => (e.toLinearEquiv : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (S p i))
        = S' p := by
      funext i
      rfl
    rw [h3] at h2
    exact h2
  -- ## 3. the frame CLM family and the projection family
  set Ψ : ℝ × ℝ → (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    spanFam S' with hΨdef
  have hΨsm : ContDiff ℝ Cin Ψ := spanFam_contDiff S' hS'
  have hΨsm' : ContDiff ℝ Cin
      (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin r) => Ψ q.1 q.2) :=
    (hΨsm.comp contDiff_fst).clm_apply contDiff_snd
  set T : ℝ × ℝ → (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
    fun p => (ContinuousLinearMap.adjoint (Ψ p)).comp (Ψ p) with hTdef
  have hadj : ContDiff ℝ Cin
      (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Ψ p)) :=
    (((ContinuousLinearMap.adjoint :
        (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗᵢ⋆[ℝ]
          (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r))).toLinearIsometry).toContinuousLinearMap).contDiff.comp
      hΨsm
  have hTsm : ContDiff ℝ Cin T := hadj.clm_comp hΨsm
  have hTquad : ∀ (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin r)),
      inner ℝ ((T p) v) v = ‖Ψ p v‖ ^ 2 := by
    intro p v
    rw [hTdef]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  set δ : ℝ × ℝ → ℝ := fun p => (T p).det with hδdef
  have hδcont : Continuous δ := ContinuousLinearMap.continuous_det.comp hTsm.continuous
  have hδpos : ∀ p ∈ Z, δ p ≠ 0 := by
    intro p hp
    have hind : Function.Injective (Ψ p) := spanFam_injective S' p (hZind' p hp)
    have hTinj : Function.Injective (T p) := by
      intro x y hxy
      have h0 : (T p) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : ‖Ψ p (x - y)‖ ^ 2 = 0 := by rw [← hTquad p (x - y), h0]; simp
      have h2 : Ψ p (x - y) = 0 := by
        have h3 : ‖Ψ p (x - y)‖ = 0 := by nlinarith [norm_nonneg (Ψ p (x - y))]
        exact norm_eq_zero.mp h3
      have h4 : x - y = 0 := hind (by rw [h2, map_zero])
      exact sub_eq_zero.mp h4
    have hker : (T p).toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hTinj
    intro hdet
    have : LinearMap.det (T p).toLinearMap = 0 := hdet
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp this) hker
  have hUopen : IsOpen {p : ℝ × ℝ | δ p ≠ 0} :=
    isOpen_ne.preimage hδcont
  obtain ⟨f, hfsm, hf01, hf1, hfsupp⟩ := bumpCompactOfOpen hZcomp hUopen
    (fun p hp => hδpos p hp)
  set lam : ℝ × ℝ → ℝ := fun p => 1 - f p with hlamdef
  have hlamsm : ContDiff ℝ Cin lam := contDiff_const.sub hfsm
  have hlamnn : ∀ p, 0 ≤ lam p := by
    intro p; rw [hlamdef]; simp only; linarith [(hf01 p).2]
  have hlam0 : ∀ p ∈ Z, lam p = 0 := by
    intro p hp
    rw [hlamdef]; simp only; rw [hf1 p hp]; ring
  have hlinj : ∀ p, lam p = 0 → Function.Injective (Ψ p) := by
    intro p hp
    have hfp : f p = 1 := by rw [hlamdef] at hp; simp only at hp; linarith
    have hmem : p ∈ Function.support f := by
      rw [Function.mem_support, hfp]; exact one_ne_zero
    have hpU : δ p ≠ 0 := hfsupp (subset_tsupport f hmem)
    have hTinj : Function.Injective (T p) := by
      refine (LinearMap.ker_eq_bot.mp ?_)
      by_contra hne
      exact hpU (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
    intro x y hxy
    have h0 : (T p) (x - y) = 0 := by
      rw [hTdef]
      simp only [ContinuousLinearMap.comp_apply, map_sub, hxy, sub_self]
    have h1 : x - y = 0 := hTinj (by rw [h0, map_zero])
    exact sub_eq_zero.mp h1
  obtain ⟨P, hPsm, hPprop⟩ := projFamilyOfVanishingLambda Ψ hΨsm' lam hlamsm hlamnn hlinj
  have hPfam : ContDiff ℝ Cin
      (P : ℝ × ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
    rw [contDiff_clm_apply_iff]
    intro v
    have h : ContDiff ℝ Cin (fun p : ℝ × ℝ => (p, v)) := contDiff_id.prodMk contDiff_const
    exact hPsm.comp h
  have hPsm' : ContDiff ℝ Cin (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => P q.1 q.2) :=
    (hPfam.comp contDiff_fst).clm_apply contDiff_snd
  -- ## 4. the mesh, the levels and the Kato chain
  obtain ⟨N, hNpos, hNmesh⟩ := meshStepBound P hPsm' hX0 (le_of_lt hMpos) hMle
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  set lev : ℕ → ℝ × ℝ → ℝ := fun j p => p.2 + (j : ℝ) / (N : ℝ) * (c p.1 - p.2) with hlevdef
  set Pj : ℕ → ℝ × ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun j p => P (p.1, lev j p) with hPjdef
  set Phi : ℕ → ℝ × ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun j p => katoMap (Pj (j+1) p) (Pj j p) with hPhidef
  have hlevsm : ∀ j, ContDiff ℝ Cin (fun p : ℝ × ℝ => lev j p) := by
    intro j
    have h : ContDiff ℝ Cin
        (fun p : ℝ × ℝ => p.2 + (j : ℝ) / (N : ℝ) * (c p.1 - p.2)) :=
      contDiff_snd.add (contDiff_const.mul ((hc.comp contDiff_fst).sub contDiff_snd))
    simpa only [lev] using h
  have hPjsm : ∀ j, ContDiff ℝ Cin (Pj j) := by
    intro j
    have h : ContDiff ℝ Cin (fun p : ℝ × ℝ => P (p.1, lev j p)) :=
      hPfam.comp (contDiff_fst.prodMk (hlevsm j))
    simpa only [Pj] using h
  have hPhism : ∀ j, ContDiff ℝ Cin (Phi j) := by
    intro j
    have h1 : ContDiff ℝ Cin (fun p : ℝ × ℝ => Pj j p * Pj (j+1) p) := by
      have := (hPjsm j).clm_comp (hPjsm (j+1))
      simpa only [ContinuousLinearMap.mul_def] using this
    have h2 : ContDiff ℝ Cin (fun p : ℝ × ℝ => (1 - Pj j p) * (1 - Pj (j+1) p)) := by
      have h1' : ContDiff ℝ Cin (fun p : ℝ × ℝ => (1 - Pj j p :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
        contDiff_const.sub (hPjsm j)
      have h2' : ContDiff ℝ Cin (fun p : ℝ × ℝ => (1 - Pj (j+1) p :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
        contDiff_const.sub (hPjsm (j+1))
      have := h1'.clm_comp h2'
      simpa only [ContinuousLinearMap.mul_def] using this
    have h3 : ContDiff ℝ Cin (fun p : ℝ × ℝ =>
        Pj j p * Pj (j+1) p + (1 - Pj j p) * (1 - Pj (j+1) p)) := h1.add h2
    simpa only [Phi, katoMap] using h3
  have hlevmem : ∀ p ∈ K, ∀ j ≤ N, (p.1, lev j p) ∈ Z := by
    intro p hp j hj
    have h2 : 0 ≤ p.2 := hindK p hp
    have h3 : p.2 ≤ c p.1 := hinter p hp
    have h4 : 0 ≤ c p.1 := le_trans h2 h3
    have hθ0 : 0 ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg N)
    have hθ1 : (j : ℝ) / (N : ℝ) ≤ 1 :=
      (div_le_one (by exact_mod_cast hNpos : (0 : ℝ) < (N : ℝ))).mpr (by exact_mod_cast hj)
    have hlin : lev j p = (1 - (j : ℝ) / (N : ℝ)) * p.2 + ((j : ℝ) / (N : ℝ)) * c p.1 := by
      rw [hlevdef]; ring
    have hmem : lev j p ∈ Set.Icc 0 (c p.1) := by
      rw [Set.mem_Icc]
      constructor
      · rw [hlin]
        have h5 : 0 ≤ 1 - (j : ℝ) / (N : ℝ) := by linarith
        exact add_nonneg (mul_nonneg h5 h2) (mul_nonneg hθ0 h4)
      · rw [hlin]
        have h6 : (1 - (j : ℝ) / (N : ℝ)) * p.2 ≤ (1 - (j : ℝ) / (N : ℝ)) * c p.1 :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        have h7 : ((j : ℝ) / (N : ℝ)) * c p.1 ≤ ((j : ℝ) / (N : ℝ)) * c p.1 := le_refl _
        nlinarith [h6, h7]
    have h1 : |p.1| ≤ X' := by
      rw [hK] at hp; exact hp.1
    rw [hZdef]
    left
    rw [hK]
    exact ⟨h1, hmem⟩
  have hPjidem : ∀ p ∈ K, ∀ j ≤ N, Pj j p * Pj j p = Pj j p := by
    intro p hp j hj
    have hmem := hlevmem p hp j hj
    have hz : lam (p.1, lev j p) = 0 := hlam0 _ hmem
    have h := (hPprop (p.1, lev j p) hz).1
    simpa only [Pj] using h
  have hPjrange : ∀ p ∈ K, ∀ j ≤ N,
      LinearMap.range ((Pj j p : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
          : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = Submodule.span ℝ (Set.range (S' (p.1, lev j p))) := by
    intro p hp j hj
    have hmem := hlevmem p hp j hj
    have hz : lam (p.1, lev j p) = 0 := hlam0 _ hmem
    have h1 : LinearMap.range ((Pj j p : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = LinearMap.range ((Ψ (p.1, lev j p)) : EuclideanSpace ℝ (Fin r) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin m)) := by
      have h := (hPprop (p.1, lev j p) hz).2
      simpa only [Pj] using h
    rw [h1]
    simpa only [Ψ] using (spanFam_range S' (p.1, lev j p))
  have hlev0 : ∀ p, lev 0 p = p.2 := by
    intro p; rw [hlevdef]; simp
  have hlevN : ∀ p, lev N p = c p.1 := by
    intro p
    simp only [hlevdef]
    rw [div_self hNne, one_mul]
    ring
  let Theta : ℕ → ℝ × ℝ →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun n => Nat.rec (fun _ => 1) (fun j rec p => rec p * Phi j p) n
  have hTheta0 : Theta 0 = fun _ : ℝ × ℝ => (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := rfl
  have hThetasu : ∀ j, Theta (j+1) = fun p => Theta j p * Phi j p := by intro j; rfl
  have hThetasm : ∀ n, ContDiff ℝ Cin (Theta n) := by
    intro n
    induction n with
    | zero => rw [hTheta0]; exact contDiff_const
    | succ j ih =>
      rw [hThetasu j]
      have := ih.clm_comp (hPhism j)
      simpa only [ContinuousLinearMap.mul_def] using this
  have hchain : ∀ p ∈ K, ∀ n ≤ N,
      Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) => Theta n p v) ∧
      LinearMap.range (((Theta n p).toLinearMap).comp ((Pj n p).toLinearMap))
        = LinearMap.range ((Pj 0 p).toLinearMap) := by
    intro p hp n hn
    induction n with
    | zero =>
      constructor
      · exact Function.bijective_id
      · have h1 : ((Theta 0 p).toLinearMap).comp ((Pj 0 p).toLinearMap)
            = (Pj 0 p).toLinearMap := by
          rw [hTheta0]; ext v; simp
        rw [h1]
    | succ j ih =>
      have hjN : j ≤ N := le_trans (Nat.le_succ j) hn
      obtain ⟨hbij, hmap⟩ := ih hjN
      have hidem' : Pj (j+1) p * Pj (j+1) p = Pj (j+1) p := hPjidem p hp (j+1) hn
      have hidem : Pj j p * Pj j p = Pj j p := hPjidem p hp j hjN
      have hnorm : ‖Pj (j+1) p - Pj j p‖ < 1 := by
        have h := hNmesh p.1 (by rw [hK] at hp; exact hp.1) p.2 (hindK p hp) (hinter p hp) j (Nat.lt_of_succ_le hn)
        have e1 : lev j p = p.2 + (j : ℝ) / (N : ℝ) * (c p.1 - p.2) := by simp only [hlevdef]
        have e2 : lev (j+1) p = p.2 + ((j : ℝ) + 1) / (N : ℝ) * (c p.1 - p.2) := by
          simp only [hlevdef, Nat.cast_add, Nat.cast_one]
        simpa only [Pj, e1, e2, norm_sub_rev] using h
      have hkato := katoStepBijective hidem' hidem hnorm
      have hkato' : Function.Bijective (fun v : EuclideanSpace ℝ (Fin m) => Phi j p v) := hkato.1
      constructor
      · have hb : Function.Bijective
            (fun v : EuclideanSpace ℝ (Fin m) => Theta j p (Phi j p v)) := hbij.comp hkato'
        simpa only [hThetasu j, mul_apply_eq_comp] using hb
      · have hstep : (Theta (j+1) p).toLinearMap
            = ((Theta j p).toLinearMap).comp ((Phi j p).toLinearMap) := by
          show ((Theta j p * Phi j p)).toLinearMap = _
          rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp]
        rw [hstep, LinearMap.comp_assoc, LinearMap.range_comp]
        have hk : LinearMap.range (((Phi j p).toLinearMap).comp ((Pj (j+1) p).toLinearMap))
            = LinearMap.range ((Pj j p).toLinearMap) := hkato.2.1
        rw [hk]
        rw [← LinearMap.range_comp]
        exact hmap
  -- ## 5. the chain is the identity at the edge points
  have hP_edge_idem : ∀ x : ℝ, |x| ≤ X' → P (x, c x) * P (x, c x) = P (x, c x) := by
    intro x hx
    have hmem : (x, c x) ∈ Z := by
      rw [hZdef]; exact Or.inr (by rw [hEdef]; exact ⟨hx, rfl⟩)
    exact (hPprop _ (hlam0 _ hmem)).1
  have hP_edge_range : ∀ x : ℝ, |x| ≤ X' →
      LinearMap.range ((P (x, c x)).toLinearMap)
        = Submodule.span ℝ (Set.range (S' (x, c x))) := by
    intro x hx
    have hmem : (x, c x) ∈ Z := by
      rw [hZdef]; exact Or.inr (by rw [hEdef]; exact ⟨hx, rfl⟩)
    have h1 : LinearMap.range ((P (x, c x)).toLinearMap)
        = LinearMap.range ((Ψ (x, c x)) : EuclideanSpace ℝ (Fin r) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin m)) := (hPprop _ (hlam0 _ hmem)).2
    rw [h1]
    simpa only [Ψ] using (spanFam_range S' (x, c x))
  have hPj_edge : ∀ x : ℝ, |x| ≤ X' → ∀ j ≤ N, Pj j (x, c x) = Pj 0 (x, c x) := by
    intro x hx j hj
    have h1 : lev j (x, c x) = c x := by simp only [hlevdef]; ring
    have h0 : lev 0 (x, c x) = c x := by simp only [hlevdef]; ring
    simp only [Pj]
    rw [h1, h0]
  have hThetaEdge : ∀ x : ℝ, |x| ≤ X' → Theta N (x, c x) = 1 := by
    intro x hx
    have hmemE : (x, c x) ∈ E := by rw [hEdef]; exact ⟨hx, rfl⟩
    have hPj0 : Pj 0 (x, c x) = P (x, c x) := by
      have h0 : lev 0 (x, c x) = c x := by simp only [hlevdef]; ring
      simp only [Pj]
      rw [h0]
    have hidem0 : Pj 0 (x, c x) * Pj 0 (x, c x) = Pj 0 (x, c x) := by
      rw [hPj0]
      exact hP_edge_idem x hx
    have hmain : ∀ n ≤ N, Theta n (x, c x) = 1 := by
      intro n hn
      induction n with
      | zero => rw [hTheta0]
      | succ j ih =>
        have hjN : j ≤ N := le_trans (Nat.le_succ j) hn
        simp only [hThetasu j]
        have hPhi_eq : Phi j (x, c x) = 1 := by
          have h1 : Pj (j+1) (x, c x) = Pj 0 (x, c x) := hPj_edge x hx (j+1) hn
          have h2 : Pj j (x, c x) = Pj 0 (x, c x) := hPj_edge x hx j hjN
          have h3 : Phi j (x, c x) = katoMap (Pj 0 (x, c x)) (Pj 0 (x, c x)) := by
            simp only [Phi]
            rw [h1, h2]
          rw [h3, katoMap_self hidem0]
        rw [ih hjN, hPhi_eq, one_mul]
    exact hmain N le_rfl
  -- ## 6. the final maps
  set W' : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m) :=
    fun p j => Theta N p (V' p.1 j) with hW'def
  have hW'sm : ∀ j, ContDiff ℝ Cin (fun p : ℝ × ℝ => W' p j) := by
    intro j
    have harg : ContDiff ℝ Cin (fun p : ℝ × ℝ => V' p.1 j) := (hV' j).comp contDiff_fst
    have h := (hThetasm N).clm_apply harg
    simpa only [W'] using h
  have hW'ind : ∀ p ∈ K, LinearIndependent ℝ (Fin.append (S' p) (W' p)) := by
    intro p hp
    have hx' : |p.1| ≤ X' := by rw [hK] at hp; exact hp.1
    have hmemZ : p ∈ Z := by rw [hZdef]; exact Or.inl hp
    obtain ⟨hbij, hmap⟩ := hchain p hp N le_rfl
    set Tr : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
      LinearEquiv.ofBijective ((Theta N p).toLinearMap) hbij with hTrdef
    have hTr_apply : ∀ v : EuclideanSpace ℝ (Fin m),
        (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) v = Theta N p v := by
      intro v; rw [hTrdef]; rfl
    have hTr_symm : ∀ v : EuclideanSpace ℝ (Fin m), Tr.symm (Theta N p v) = v := by
      intro v; rw [← hTr_apply v]; exact Tr.symm_apply_apply v
    have hspan_p : Submodule.span ℝ (Set.range (S' p))
        = LinearMap.range ((Pj 0 p).toLinearMap) := by
      have h := hPjrange p hp 0 (Nat.zero_le N)
      rw [h, hlev0 p]
    have hspan_e : Submodule.span ℝ (Set.range (S' (p.1, c p.1)))
        = LinearMap.range ((Pj N p).toLinearMap) := by
      have h1 : Pj N p = P (p.1, c p.1) := by simp only [Pj, hlevN p]
      rw [h1]
      exact (hP_edge_range p.1 hx').symm
    have hkey : Submodule.span ℝ (Set.range (fun i : Fin r => Tr.symm (S' p i)))
        = Submodule.span ℝ (Set.range (S' (p.1, c p.1))) := by
      have h1 : Submodule.span ℝ (Set.range (fun i : Fin r => Tr.symm (S' p i)))
          = Submodule.map Tr.symm.toLinearMap
              (Submodule.span ℝ (Set.range (S' p))) := by
        have hset : Set.range (fun i : Fin r => Tr.symm (S' p i))
            = Tr.symm.toLinearMap '' Set.range (S' p) := by
          ext y; constructor
          · rintro ⟨i, rfl⟩; exact ⟨S' p i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨w, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
        rw [hset, Submodule.span_image]
      rw [h1, hspan_p]
      have hid : (Tr.symm.toLinearMap).comp ((Theta N p).toLinearMap) = LinearMap.id :=
        LinearMap.ext (fun v => hTr_symm v)
      have h2 : Submodule.map Tr.symm.toLinearMap (LinearMap.range ((Pj 0 p).toLinearMap))
          = LinearMap.range ((Pj N p).toLinearMap) := by
        calc Submodule.map Tr.symm.toLinearMap (LinearMap.range ((Pj 0 p).toLinearMap))
            = Submodule.map Tr.symm.toLinearMap
                (Submodule.map ((Theta N p).toLinearMap)
                  (LinearMap.range ((Pj N p).toLinearMap))) := by
                rw [← hmap, LinearMap.range_comp]
          _ = Submodule.map ((Tr.symm.toLinearMap).comp ((Theta N p).toLinearMap))
                (LinearMap.range ((Pj N p).toLinearMap)) := by
                rw [Submodule.map_comp]
          _ = Submodule.map LinearMap.id (LinearMap.range ((Pj N p).toLinearMap)) := by
                rw [hid]
          _ = LinearMap.range ((Pj N p).toLinearMap) := Submodule.map_id _
      rw [h2, hspan_e]
    have hu : LinearIndependent ℝ (fun i : Fin r => Tr.symm (S' p i)) := by
      have h1 : LinearIndependent ℝ (S' p) := hZind' p hmemZ
      have h := LinearIndependent.map' h1 Tr.symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr Tr.symm.injective)
      rw [show (fun i : Fin r => Tr.symm (S' p i)) = Tr.symm.toLinearMap ∘ S' p from rfl]
      exact h
    have hu' : LinearIndependent ℝ (S' (p.1, c p.1)) := by
      have hmem : (p.1, c p.1) ∈ Z := by
        rw [hZdef]; exact Or.inr (by rw [hEdef]; exact ⟨hx', rfl⟩)
      exact hZind' _ hmem
    have hhedge : LinearIndependent ℝ (Fin.append (S' (p.1, c p.1)) (V' p.1)) := by
      have h1 : LinearIndependent ℝ (Fin.append (S (p.1, c p.1)) (V p.1)) := hedge p.1 hx'
      have h2 : LinearIndependent ℝ (Fin.append (fun i : Fin r => e (S (p.1, c p.1) i))
          (fun j : Fin k => e (V p.1 j))) := by
        have h := (appendMapInjective (T := (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))
          (fun a b hab => e.injective hab) (S (p.1, c p.1)) (V p.1)).mpr h1
        rw [show (Fin.append (fun i : Fin r => (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
              (S (p.1, c p.1) i)) (fun j : Fin k => (e : F →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
              (V p.1 j)))
            = Fin.append (fun i : Fin r => e (S (p.1, c p.1) i))
              (fun j : Fin k => e (V p.1 j)) from rfl] at h
        exact h
      rwa [show (Fin.append (fun i : Fin r => e (S (p.1, c p.1) i))
          (fun j : Fin k => e (V p.1 j))) = Fin.append (S' (p.1, c p.1)) (V' p.1) from rfl] at h2
    have hw : LinearIndependent ℝ (Fin.append (fun i : Fin r => Tr.symm (S' p i)) (V' p.1)) :=
      (appendSpanCongr hu hu' hkey (V' p.1)).mpr hhedge
    have hTrinj : Function.Injective (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
      intro a b hab
      exact Tr.injective hab
    have hfin : LinearIndependent ℝ
        (Fin.append (fun i : Fin r => (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
            (Tr.symm (S' p i)))
          (fun j : Fin k => (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
            (V' p.1 j))) :=
      (appendMapInjective (T := (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))
        hTrinj (fun i : Fin r => Tr.symm (S' p i)) (V' p.1)).mpr hw
    have hfun : (Fin.append (fun i : Fin r => (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin m)) (Tr.symm (S' p i)))
        (fun j : Fin k => (Tr : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
          (V' p.1 j))) = Fin.append (S' p) (W' p) := by
      funext x
      revert x
      refine Fin.addCases ?_ ?_
      · intro i
        simp only [Fin.append_left]
        exact Tr.apply_symm_apply (S' p i)
      · intro j
        simp only [Fin.append_right, W']
        rw [hTr_apply]
    rw [hfun] at hfin
    exact hfin
  -- ## 7. transport back to `F`
  refine ⟨fun p j => e.symm (W' p j), ?_, ?_, ?_⟩
  · refine contDiff_pi.mpr ?_
    intro j
    exact (LinearIsometryEquiv.contDiff e.symm).comp (hW'sm j)
  · intro x hx
    funext j
    have h1 : Theta N (x, c x) = 1 := hThetaEdge x hx
    simp only [W', V']
    rw [h1]
    simp
  · intro p hp
    have h1 : LinearIndependent ℝ (Fin.append (S' p) (W' p)) := hW'ind p hp
    have h2 : LinearIndependent ℝ
        (Fin.append (fun i : Fin r => e.symm (S' p i)) (fun j : Fin k => e.symm (W' p j))) := by
      have h := (appendMapInjective (T := (e.symm : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] F))
        (fun a b hab => e.symm.injective hab) (S' p) (W' p)).mpr h1
      rw [show (Fin.append (fun i : Fin r => (e.symm : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] F) (S' p i))
            (fun j : Fin k => (e.symm : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] F) (W' p j)))
          = Fin.append (fun i : Fin r => e.symm (S' p i)) (fun j : Fin k => e.symm (W' p j))
          from rfl] at h
      exact h
    have hid3 : (fun i : Fin r => e.symm (S' p i)) = S p := by
      funext i
      simp only [S', LinearIsometryEquiv.symm_apply_apply]
    rw [hid3] at h2
    exact h2

end Work.Drive.Whitney
