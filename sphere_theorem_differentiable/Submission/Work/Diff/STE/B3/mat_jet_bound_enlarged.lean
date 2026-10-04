import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.B3.MatGlob.isCompact_uniform_bound
import Submission.Work.Diff.STE.B3.MatGlob.mat_expansion
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.transport_exists_cutoff
import Submission.Work.Diff.STE.B3.pdVec_mul_comp_le
import Submission.Work.Diff.STE.Lead.Gal.CompJetAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Auxiliary lemmas -/

/-- **Complexification does not change the norm of the iterated Fréchet derivative.** -/
lemma norm_iteratedFDeriv_ofReal_comp {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖
      = ‖iteratedFDeriv ℝ i f x‖ := by
  have hle : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (f := f) (𝕜 := ℝ) hf (i := i) hle
  have h2 : (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) = ⇑Complex.ofRealLI ∘ f := rfl
  rw [h2]
  exact h

/-- From a `pdVec`-bound for the complexification of a real-valued function we get a bound for the
norm of the whole iterated Fréchet derivative. -/
lemma iteratedFDeriv_le_of_pdVec_ofReal {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {m : ℕ} {B : ℝ} (hB : 0 ≤ B) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (h : ∀ (m' : ℕ), m' ≤ m → ∀ γ : Fin m' → Fin n,
      ‖Work.Diff.STE.pdVec m' γ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x‖ ≤ B) :
    ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ ((n : ℝ) + 1) ^ m * B := by
  intro i hi
  have hb : ∀ γ : Fin i → Fin n,
      ‖iteratedFDeriv ℝ i f x (fun j => Pi.single (γ j) (1 : ℝ))‖ ≤ B := by
    intro γ
    have h1 := h i hi γ
    rw [Work.Diff.STE.B3.pdVec_ofReal_eq hf i γ, Complex.norm_real] at h1
    exact h1
  have h2 := Work.Diff.STE.B3.norm_multilinear_le_of_basis (Φ := iteratedFDeriv ℝ i f x) hB hb
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn2 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ (n : ℝ) ^ i * B := h2
    _ ≤ ((n : ℝ) + 1) ^ i * B :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hn2 i) hB
    _ ≤ ((n : ℝ) + 1) ^ m * B :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn hi) hB

/-- The jet towers of a function smooth at `x` are controlled on a neighbourhood of `x`. -/
lemma eventually_iteratedFDeriv_norm_lt {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (Fin n → ℝ) → F} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (i : ℕ) :
    ∀ᶠ y in nhds x, ‖iteratedFDeriv ℝ i f y‖ < ‖iteratedFDeriv ℝ i f x‖ + 1 := by
  have hle : (0 : WithTop ℕ∞) + (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [zero_add]
    exact WithTop.coe_le_coe.mpr le_top
  have h : ContDiffAt ℝ (0 : WithTop ℕ∞) (iteratedFDeriv ℝ i f) x :=
    hf.iteratedFDeriv_right (m := 0) (i := i) hle
  exact h.continuousAt.norm.eventually_lt continuousAt_const (by linarith)

/-- Evaluation of an iterated derivative on a tuple of standard basis vectors. -/
lemma eval_basis_le {n k : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin n → ℝ) → F} (x : Fin n → ℝ) (γ : Fin k → Fin n) :
    ‖iteratedFDeriv ℝ k f x (fun j => Pi.single (γ j) (1 : ℝ))‖
      ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ k f x)
    (fun j : Fin k => (Pi.single (γ j) (1 : ℝ) : Fin n → ℝ))
  have hprod : ∏ j : Fin k, ‖(Pi.single (γ j) (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
    simp [Pi.norm_single]
  rwa [hprod, mul_one] at h

/-- **`pdVec` only depends on the germ.**  Two functions that agree on an open set containing `x`
and are smooth at `x` have the same iterated partial derivatives at `x`. -/
lemma pdVec_congr_of_eqOn {n : ℕ} {f g : (Fin n → ℝ) → ℂ} {s : Set (Fin n → ℝ)}
    (hs : IsOpen s) {x : Fin n → ℝ} (hx : x ∈ s)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (h : Set.EqOn f g s) (m : ℕ) (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β f x = Work.Diff.STE.pdVec m β g x := by
  rw [Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at hf m β,
    Work.Diff.STE.B3.pdVec_eq_iteratedFDeriv_at hg m β]
  rw [← iteratedFDerivWithin_of_isOpen m hs hx, ← iteratedFDerivWithin_of_isOpen m hs hx]
  exact congrArg (fun Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin n → ℝ) ℂ =>
      Φ (fun j => Pi.single (β j) (1 : ℝ)))
    (iteratedFDerivWithin_congr h hx m)

/-- **Flat-space composite jet bound (auxiliary form).** -/
theorem pdVec_ofReal_sum_mul_comp_le_aux {n : ℕ} {κ : Type*} [Fintype κ] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s t : Set (Fin n → ℝ)) (hs : IsOpen s) (ht : IsOpen t)
        (P Q : κ → (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
        (x : Fin n → ℝ) (β : Fin m → Fin n) (MP MD MQ : ℝ),
        (0 ≤ MP) → (0 ≤ MD) → (0 ≤ MQ) → x ∈ s → Set.MapsTo φ s t →
        (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (P a) s) →
        (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (Q a) t) →
        (ContDiffOn ℝ (⊤ : ℕ∞) φ s) →
        (∀ a (m' : ℕ), m' ≤ m → ∀ γ : Fin m' → Fin n,
          ‖Work.Diff.STE.pdVec m' γ (fun y : Fin n → ℝ => ((P a y : ℝ) : ℂ)) x‖ ≤ MP) →
        (∀ a (m' : ℕ), m' ≤ m → ∀ γ : Fin m' → Fin n,
          ‖Work.Diff.STE.pdVec m' γ (fun y : Fin n → ℝ => ((Q a y : ℝ) : ℂ)) (φ x)‖ ≤ MQ) →
        (∀ i : ℕ, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ x‖ ≤ MD ^ i) →
        ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ =>
          ((∑ a : κ, P a z * Q a (φ z) : ℝ) : ℂ)) x‖ ≤ C * MP * (1 + MD) ^ m * MQ := by
  classical
  obtain ⟨C0, hC0nn, hC0⟩ := Work.Diff.STE.B3.pdVec_mul_comp_le (n := n) (m := m)
  refine ⟨(Fintype.card κ : ℝ) * (n : ℝ) ^ m * (((n : ℝ) + 1) ^ m) ^ 2 * C0, by positivity, ?_⟩
  intro s t hs ht P Q φ x β MP MD MQ hMP hMD hMQ hxs hst hPon hQon hφon hPjet hQjet hφjet
  have hPat : ∀ a, ContDiffAt ℝ (⊤ : ℕ∞) (P a) x :=
    fun a => (hPon a).contDiffAt (hs.mem_nhds hxs)
  have hφat : ContDiffAt ℝ (⊤ : ℕ∞) φ x := hφon.contDiffAt (hs.mem_nhds hxs)
  have hφx : φ x ∈ t := hst hxs
  have hQat : ∀ a, ContDiffAt ℝ (⊤ : ℕ∞) (Q a) (φ x) :=
    fun a => (hQon a).contDiffAt (ht.mem_nhds hφx)
  have hPit : ∀ a, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (P a) x‖ ≤ ((n : ℝ) + 1) ^ m * MP :=
    fun a i hi => iteratedFDeriv_le_of_pdVec_ofReal hMP (hPat a) (fun m' hm' γ => hPjet a m' hm' γ) i hi
  have hQit : ∀ a, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (Q a) (φ x)‖ ≤ ((n : ℝ) + 1) ^ m * MQ :=
    fun a i hi => iteratedFDeriv_le_of_pdVec_ofReal hMQ (hQat a) (fun m' hm' γ => hQjet a m' hm' γ) i hi
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp
    (hφat.continuousAt.preimage_mem_nhds (ht.mem_nhds hφx))
  set U : Set (Fin n → ℝ) := s ∩ W with hUdef
  have hUopen : IsOpen U := hs.inter hWopen
  have hxU : x ∈ U := ⟨hxs, hxW⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  obtain ⟨ρ, hρsm, -, hρ1, hρsupp⟩ := Work.Diff.STE.B3.transport_exists_cutoff
    (Metric.closedBall x (ε / 2)) U (isCompact_closedBall x (ε / 2)) hUopen
    (fun y hy => hεU (Metric.closedBall_subset_ball (x := x) (by linarith) hy))
  obtain ⟨ε', hε', hε't⟩ := Metric.mem_nhds_iff.mp (ht.mem_nhds hφx)
  obtain ⟨θ, hθsm, -, hθ1, hθsupp⟩ := Work.Diff.STE.B3.transport_exists_cutoff
    (Metric.closedBall (φ x) (ε' / 2)) t (isCompact_closedBall (φ x) (ε' / 2)) ht
    (fun y hy => hε't (Metric.closedBall_subset_ball (x := φ x) (by linarith) hy))
  have hρev : ρ =ᶠ[nhds x] (fun _ : Fin n → ℝ => (1 : ℝ)) := by
    filter_upwards [Metric.closedBall_mem_nhds x (show (0 : ℝ) < ε / 2 by linarith)] with z hz
    exact hρ1 z hz
  have hθev : θ =ᶠ[nhds (φ x)] (fun _ : Fin n → ℝ => (1 : ℝ)) := by
    filter_upwards [Metric.closedBall_mem_nhds (φ x) (show (0 : ℝ) < ε' / 2 by linarith)] with u hu
    exact hθ1 u hu
  have hρx : ρ x = 1 := hρev.eq_of_nhds
  have hPtsm : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ρ z • P a z) := fun a =>
    Work.Diff.STE.Lead.Gal.contDiff_smul_of_tsupport_subset hUopen
      ((hPon a).mono Set.inter_subset_left) hρsm hρsupp
  have hQtsm : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (fun u : Fin n → ℝ => θ u • Q a u) := fun a =>
    Work.Diff.STE.Lead.Gal.contDiff_smul_of_tsupport_subset ht (hQon a) hθsm hθsupp
  have hφtsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ρ z • φ z) :=
    Work.Diff.STE.Lead.Gal.contDiff_smul_of_tsupport_subset hUopen
      (hφon.mono Set.inter_subset_left) hρsm hρsupp
  have hPteq : ∀ a, (fun z : Fin n → ℝ => ρ z • P a z) =ᶠ[nhds x] P a := fun a =>
    hρev.mono fun z hz => by simp only [hz, one_smul]
  have hQteq : ∀ a, (fun u : Fin n → ℝ => θ u • Q a u) =ᶠ[nhds (φ x)] Q a := fun a =>
    hθev.mono fun u hu => by simp only [hu, one_smul]
  have hφteq : (fun z : Fin n → ℝ => ρ z • φ z) =ᶠ[nhds x] φ :=
    hρev.mono fun z hz => by simp only [hz, one_smul]
  have hPtit : ∀ a, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun z : Fin n → ℝ => ρ z • P a z) x‖
      ≤ ((n : ℝ) + 1) ^ m * MP := fun a i hi => by
    rw [((hPteq a).iteratedFDeriv ℝ i).eq_of_nhds]
    exact hPit a i hi
  have hQit' : ∀ a, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun u : Fin n → ℝ => θ u • Q a u) (φ x)‖
      ≤ ((n : ℝ) + 1) ^ m * MQ := fun a i hi => by
    rw [((hQteq a).iteratedFDeriv ℝ i).eq_of_nhds]
    exact hQit a i hi
  have hφit : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i (fun z : Fin n → ℝ => ρ z • φ z) x‖
      ≤ MD ^ i := fun i h1 h2 => by
    rw [(hφteq.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hφjet i h1 h2
  have hFAsm : ∀ a, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) := fun a =>
    Complex.ofRealCLM.contDiff.comp ((hPtsm a).mul ((hQtsm a).comp hφtsm))
  have hGA : ∀ a : κ, ∀ γ : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m γ
        (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x‖
        ≤ C0 * (((n : ℝ) + 1) ^ m * MP) * (1 + MD) ^ m * (((n : ℝ) + 1) ^ m * MQ) := by
    intro a γ
    have hfun : (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ))
        = fun z : Fin n → ℝ =>
          (fun z : Fin n → ℝ => ((ρ z • P a z : ℝ) : ℂ)) z
            * (fun u : Fin n → ℝ => ((θ u • Q a u : ℝ) : ℂ)) ((fun z : Fin n → ℝ => ρ z • φ z) z) := by
      funext z
      simp only [Complex.ofReal_mul]
    rw [hfun]
    exact hC0 (fun z : Fin n → ℝ => ((ρ z • P a z : ℝ) : ℂ))
      (fun z : Fin n → ℝ => ρ z • φ z) (fun u : Fin n → ℝ => ((θ u • Q a u : ℝ) : ℂ)) x γ
      (((n : ℝ) + 1) ^ m * MP) MD (((n : ℝ) + 1) ^ m * MQ)
      (Complex.ofRealCLM.contDiff.comp (hPtsm a)) hφtsm
      (Complex.ofRealCLM.contDiff.comp (hQtsm a))
      (fun i _ => by
        rw [norm_iteratedFDeriv_ofReal_comp (hPtsm a).contDiffAt i]
        exact hPtit a i ‹i ≤ m›)
      (fun i h1 h2 => hφit i h1 h2)
      (fun i _ => by
        simp only [hρx, one_smul]
        rw [norm_iteratedFDeriv_ofReal_comp (hQtsm a).contDiffAt i]
        exact hQit' a i ‹i ≤ m›)
  have hGcsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ∑ a : κ,
      ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) :=
    ContDiff.sum (s := Finset.univ) (fun a _ => hFAsm a)
  have hsum : iteratedFDeriv ℝ m (fun z : Fin n → ℝ => ∑ a : κ,
        ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x
      = ∑ a : κ, iteratedFDeriv ℝ m
          (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x := by
    have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (u := Finset.univ)
      (f := fun a z => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) (n := m) (x := x)
      (fun a _ => (hFAsm a).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    simpa using h
  set G : (Fin n → ℝ) → ℝ := fun z => ∑ a : κ, P a z * Q a (φ z) with hGdef
  have hGsm : ContDiffAt ℝ (⊤ : ℕ∞) G x := by
    have h := ContDiffAt.sum (s := Finset.univ) (f := fun a z => P a z * Q a (φ z))
      (fun a _ => (hPat a).mul ((hQat a).comp x hφat))
    simpa only [hGdef] using h
  have hGeq : (fun z : Fin n → ℝ => ((G z : ℝ) : ℂ)) =ᶠ[nhds x]
      (fun z : Fin n → ℝ => ∑ a : κ,
        ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) := by
    have hθφ : ∀ᶠ z in nhds x, θ (φ z) = 1 := hφat.continuousAt.eventually hθev
    filter_upwards [hρev, hθφ] with z hz1 hz2
    simp only [hGdef]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hz1, hz2, one_smul]
  have hmain : ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((G z : ℝ) : ℂ)) x‖
      ≤ (Fintype.card κ : ℝ) * (n : ℝ) ^ m * (((n : ℝ) + 1) ^ m) ^ 2 * C0 * MP * (1 + MD) ^ m * MQ := by
    rw [Work.Diff.STE.B3.pdVec_ofReal_eq hGsm m β, Complex.norm_real]
    calc ‖iteratedFDeriv ℝ m G x (fun j => Pi.single (β j) (1 : ℝ))‖
        ≤ ‖iteratedFDeriv ℝ m G x‖ := eval_basis_le x β
      _ = ‖iteratedFDeriv ℝ m (fun z : Fin n → ℝ => ((G z : ℝ) : ℂ)) x‖ :=
          (norm_iteratedFDeriv_ofReal_comp hGsm m).symm
      _ = ‖iteratedFDeriv ℝ m (fun z : Fin n → ℝ => ∑ a : κ,
            ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x‖ := by
          rw [(hGeq.iteratedFDeriv ℝ m).eq_of_nhds]
      _ ≤ ‖∑ a : κ, iteratedFDeriv ℝ m
            (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x‖ := by
          rw [hsum]
      _ ≤ ∑ a : κ, ‖iteratedFDeriv ℝ m
            (fun z : Fin n → ℝ => ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a : κ, ((n : ℝ) ^ m * (C0 * (((n : ℝ) + 1) ^ m * MP) * (1 + MD) ^ m
            * (((n : ℝ) + 1) ^ m * MQ))) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact Work.Diff.STE.B3.norm_multilinear_le_of_basis
            (Φ := iteratedFDeriv ℝ m (fun z : Fin n → ℝ =>
              ((ρ z • P a z * (θ (ρ z • φ z) • Q a (ρ z • φ z)) : ℝ) : ℂ)) x)
            (B := C0 * (((n : ℝ) + 1) ^ m * MP) * (1 + MD) ^ m * (((n : ℝ) + 1) ^ m * MQ))
            (by positivity)
            (fun γ => by
              rw [← Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ (hFAsm a) x γ]
              exact hGA a γ)
      _ = (Fintype.card κ : ℝ) * (n : ℝ) ^ m * (((n : ℝ) + 1) ^ m) ^ 2 * C0 * MP * (1 + MD) ^ m * MQ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  simpa only [hGdef] using hmain

/-- The section class admitted by `mat_jet_bound_enlarged`. -/
def PackJet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (K : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : Prop :=
  (∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) ∧
  Work.Diff.STE.D.ChartData (I := I) (M := M) h ∧
  (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i →
      ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)

/-- **The enlargement margin for the flat balls.** -/
private lemma delta_target_ball_aux (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ j + δ →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := by
  classical
  have hmargin : ∀ j : ι₀, ∃ δj : ℝ, 0 < δj ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δj →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := by
    intro j
    have hA : IsCompact {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j} := by
      rw [show {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ ≤ 2 * D.σ j}
          = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) from by
        ext z; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]]
      exact isCompact_closedBall _ _
    have hTopen : IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹'
        (extChartAt I (D.x₀ j)).target) :=
      (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
        (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous
    obtain ⟨δj, hδjpos, hδjsub⟩ :=
      hA.exists_cthickening_subset_open hTopen (fun z hz => D.htarget j z hz)
    refine ⟨δj, hδjpos, fun z hz => hδjsub ?_⟩
    by_cases hle : ‖z‖ ≤ 2 * D.σ j
    · exact Metric.mem_cthickening_of_dist_le z z δj _ hle (by rw [dist_self]; exact hδjpos.le)
    · push_neg at hle
      have hσpos : 0 < 2 * D.σ j := by have := D.hσ j; linarith
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hσpos hle.le
      have hmem : ((2 * D.σ j / ‖z‖) • z) ∈ {z : Fin (Module.finrank ℝ E) → ℝ |
          ‖z‖ ≤ 2 * D.σ j} := by
        simp only [Set.mem_setOf_eq]
        rw [norm_smul, Real.norm_of_nonneg (by positivity),
          div_mul_cancel₀ (2 * D.σ j) hzpos.ne']
      refine Metric.mem_cthickening_of_dist_le z ((2 * D.σ j / ‖z‖) • z) δj _ hmem ?_
      have hvec : (1 - 2 * D.σ j / ‖z‖) • z = z - (2 * D.σ j / ‖z‖) • z := by
        rw [sub_smul, one_smul]
      have hnorm : ‖z - (2 * D.σ j / ‖z‖) • z‖ = ‖z‖ - 2 * D.σ j := by
        rw [← hvec, norm_smul,
          Real.norm_of_nonneg (by rw [sub_nonneg, div_le_one hzpos]; exact hle.le),
          sub_mul, one_mul, div_mul_cancel₀ (2 * D.σ j) hzpos.ne']
      rw [dist_eq_norm, hnorm]
      linarith
  by_cases hne : Nonempty ι₀
  · haveI : Nonempty ι₀ := hne
    choose δj hδjpos hδjmarg using hmargin
    refine ⟨Finset.univ.inf' Finset.univ_nonempty δj, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hδjpos i)
    · intro j z hz
      exact hδjmarg j z (le_trans hz (by linarith [Finset.inf'_le δj (Finset.mem_univ j)]))
  · exact ⟨1, one_pos, fun j => (hne ⟨j⟩).elim⟩


/-- **Uniform jet bounds for the chart matrix beyond the `2σ`-ball.**

`D.mat j h c d z` is the chart matrix of the section `h` in the `g₀`-orthonormal frame `e j ·`.  The
hypothesis `hjet` bounds its `pdVec`-jets up to order `k+1` by `K` on the closed `2σ i`-ball of every
chart `i`.  This result produces `δ > 0` and `C` (depending only on `D`, `k`, `K`, never on `h`) such
that the same jets are bounded by `C` on the enlarged ball `‖z‖ ≤ 2 σ j + δ`.

ROUTE.  Fix `j`, `c`, `d`, `m ≤ k+1`, `β` and `z` with `‖z‖ ≤ 2 σ j + δ`.
(1) `D.hcover` gives a chart `i` with `D.pt j z` in the chart-`i` source and
`‖D.coord i (D.pt j z)‖ < D.σ i ≤ 2 * D.σ i`.
(2) On a neighbourhood `U` of `z` small enough that `‖D.coord i (D.pt j y)‖ ≤ 2 * D.σ i` there, the
cross-chart expansion (the proved `Work.Diff.STE.B3.MatGlob.mat_expansion`) gives
`D.mat j h c d y = ∑ a, ∑ b, Θa y * Θb y * D.mat i h a b (T y)`, where `T y := D.coord i (D.pt j y)`
and `Θa y := g₀.inner (D.pt j y) (D.e j c (D.pt j y)) (D.e i a (D.pt j y))`.  Both `T` and the `Θa`
are smooth and `h`-independent on `U`.
(3) Absorb the product into the outer map: with `f y := (T y, y)` and
`g (u, y) := Θa y * Θb y * (D.mat i h a b u)`, the proved Faà di Bruno bound
`Work.Diff.STE.flat.norm_iteratedFDeriv_comp_le_of_contDiffAt_ste` gives
`‖D^m (g ∘ f) y‖ ≤ m! * Cf * Df^m`, where `Cf` bounds the jets of `g` at `(T y, y)` — built from the
jets of `Θa`, `Θb` at `y` (fixed) and the jets of `D.mat i h a b` at `T y`, which are `≤ K` by
`hjet` after converting `pdVec` bounds to `iteratedFDeriv` bounds with the proved
`Work.Diff.STE.Lead.Gal.pdVec_eq_iteratedFDeriv_on` and
`Work.Diff.STE.B3.norm_multilinear_le_of_basis` — and `Df` bounds the jets of `f` at `y` (jets of
`T` at `y`, fixed, plus the identity).  Convert back with `pdVec_eq_iteratedFDeriv_on`.
(4) The bound of (3) depends on `z` only through fixed functions and their jets on a neighbourhood of
`z`, hence is uniform in `h`; the proved `Work.Diff.STE.B3.MatGlob.isCompact_uniform_bound` turns
these pointwise neighbourhood bounds into a single `C` on the compact enlarged ball.  Choose `δ` so
that the enlarged ball lies in `flatToE (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target`
(`Work.Diff.STE.B3.MatGlob.exists_delta_target_frame`; the private `delta_target_frame_priv` of
`Submission/Work/Diff/STE/B3/mat_jet_bound_global.lean` proves it, and that file also contains the
proved `m ≤ 1` case of this claim together with the shape of step (3)). -/
theorem mat_jet_bound_enlarged
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
          (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (j : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
          (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ j + δ →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat j h c d y : ℝ) : ℂ)) z‖ ≤ C := by
  classical
  by_cases hι : Nonempty ι₀
  · by_cases hfin : Module.finrank ℝ E = 0
    · refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
      intro h hsym hsmooth hjet j c d m hm β z hz
      exact absurd c.isLt (by omega)
    · haveI : Nonempty ι₀ := hι
      haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hfin⟩⟩
      obtain ⟨δ, hδpos, hδtarget⟩ := delta_target_ball_aux (I := I) (M := M) D
      -- ## the local bound at a point of the enlarged ball
      have hloc : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j + δ)
          (c d : Fin (Module.finrank ℝ E)),
          ∃ C : ℝ, 0 ≤ C ∧ ∃ u ∈ nhds z, ∀ y ∈ u, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
            PackJet (I := I) (M := M) D k K h →
            ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat j h c d y : ℝ) : ℂ)) y‖ ≤ C := by
        intro j z hz c d
        obtain ⟨i, hsrc, hcoord⟩ := D.hcover (D.pt j z)
        have hτz : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ 2 * D.σ i := by
          have := D.hσ i; linarith
        have hzgood : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := by
          refine ⟨?_, hsrc, ?_⟩
          · rw [IsOpen.interior_eq (isOpen_extChartAt_target (I := I) (D.x₀ j))]
            exact hδtarget j z hz
          · rw [IsOpen.interior_eq (isOpen_extChartAt_target (I := I) (D.x₀ i)),
              ← noT2_flatToE_coord (I := I) (M := M) D i hsrc]
            exact D.htarget i _ hτz
        set A : Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
          fun a w => g₀.inner (D.pt j w) (D.e j c (D.pt j w)) (D.e i a (D.pt j w)) with hA
        set B : Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
          fun b w => g₀.inner (D.pt j w) (D.e j d (D.pt j w)) (D.e i b (D.pt j w)) with hB
        set T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
          Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j with hT
        have hTapply : ∀ w, T w = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j w) := fun w => by
          simp only [hT, Work.Diff.STE.D.tMapFun_apply]
        have hTzlt : ‖T z‖ < 2 * D.σ i := by
          rw [hTapply z]; linarith [D.hσ i]
        set Gs : Set (Fin (Module.finrank ℝ E) → ℝ) :=
          Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∩ {w | ‖T w‖ < 2 * D.σ i} with hGs
        have hzGs : z ∈ Gs := ⟨hzgood, hTzlt⟩
        have hGsopen : IsOpen Gs := by
          rw [isOpen_iff_mem_nhds]
          rintro w ⟨hw1, hw2⟩
          exact Filter.inter_mem ((noT2_isOpen_goodSet (I := I) (M := M) D i j).mem_nhds hw1)
            (((noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hw1).continuousAt.norm).eventually_lt
              continuousAt_const hw2)
        set t : Set (Fin (Module.finrank ℝ E) → ℝ) := {u |
          Work.Diff.STE.flatToE (I := I) (D.x₀ i) u ∈ interior ((extChartAt I (D.x₀ i)).target)}
          with ht
        have htopen : IsOpen t :=
          isOpen_interior.preimage (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ i)).continuous
        have hst : Set.MapsTo T Gs t := fun w hw => by
          show Work.Diff.STE.flatToE (I := I) (D.x₀ i) (T w)
            ∈ interior ((extChartAt I (D.x₀ i)).target)
          rw [hTapply w, noT2_flatToE_coord (I := I) (M := M) D i hw.1.2.1]
          exact hw.1.2.2
        set U : Set (Fin (Module.finrank ℝ E) → ℝ) := Gs
            ∩ (⋂ i' : Fin (k + 2), ⋂ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                {y | ‖iteratedFDeriv ℝ i'.val (A q.1 * B q.2) y‖
                  < ‖iteratedFDeriv ℝ i'.val (A q.1 * B q.2) z‖ + 1})
            ∩ (⋂ i' : Fin (k + 2),
                {y | ‖iteratedFDeriv ℝ i'.val T y‖ < ‖iteratedFDeriv ℝ i'.val T z‖ + 1}) with hU
        have hUmem : U ∈ nhds z := by
          refine Filter.inter_mem (Filter.inter_mem (hGsopen.mem_nhds hzGs) ?_) ?_
          · refine Filter.iInter_mem.mpr fun i' => Filter.iInter_mem.mpr fun q => ?_
            have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (A q.1 * B q.2) z :=
              ((noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j c q.1 hzgood).mul
                (noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j d q.2 hzgood))
            exact eventually_iteratedFDeriv_norm_lt hsm i'.val
          · refine Filter.iInter_mem.mpr fun i' => ?_
            exact eventually_iteratedFDeriv_norm_lt
              (noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hzgood) i'.val
        set MP : ℝ := max 1 (Finset.univ.sup' Finset.univ_nonempty
            (fun q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
              Finset.univ.sup' Finset.univ_nonempty (fun i' : Fin (k + 2) =>
                ‖iteratedFDeriv ℝ i'.val (A q.1 * B q.2) z‖ + 1))) with hMP
        set MD : ℝ := max 1 (Finset.univ.sup' Finset.univ_nonempty
            (fun i' : Fin (k + 2) => ‖iteratedFDeriv ℝ i'.val T z‖ + 1)) with hMD
        have hMPnn : 0 ≤ MP := by rw [hMP]; exact le_trans zero_le_one (le_max_left _ _)
        have hMD1 : 1 ≤ MD := by rw [hMD]; exact le_max_left _ _
        have hMDnn : 0 ≤ MD := le_trans zero_le_one hMD1
        have hAsm : ∀ a : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞) (A a) Gs := fun a =>
          fun w hw => (noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j c a hw.1).mono
            (Set.subset_univ Gs)
        have hBsm : ∀ b : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞) (B b) Gs := fun b =>
          fun w hw => (noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j d b hw.1).mono
            (Set.subset_univ Gs)
        have hTsm : ContDiffOn ℝ (⊤ : ℕ∞) T Gs := fun w hw =>
          (noT2_tMapFun_contDiffAt (I := I) (M := M) D i j hw.1).mono (Set.subset_univ Gs)
        -- the constants of the composite bound
        have hCml : ∀ m' : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            (∀ (s t : Set (Fin (Module.finrank ℝ E) → ℝ)) (hs : IsOpen s) (ht : IsOpen t)
              (P Q : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
                (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
              (φ : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
              (x : Fin (Module.finrank ℝ E) → ℝ) (β : Fin m' → Fin (Module.finrank ℝ E))
              (MP' MD' MQ' : ℝ),
              (0 ≤ MP') → (0 ≤ MD') → (0 ≤ MQ') → x ∈ s → Set.MapsTo φ s t →
              (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (P a) s) →
              (∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (Q a) t) →
              (ContDiffOn ℝ (⊤ : ℕ∞) φ s) →
              (∀ a (m'' : ℕ), m'' ≤ m' → ∀ γ : Fin m'' → Fin (Module.finrank ℝ E),
                ‖Work.Diff.STE.pdVec m'' γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((P a y : ℝ) : ℂ)) x‖ ≤ MP') →
              (∀ a (m'' : ℕ), m'' ≤ m' → ∀ γ : Fin m'' → Fin (Module.finrank ℝ E),
                ‖Work.Diff.STE.pdVec m'' γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Q a y : ℝ) : ℂ)) (φ x)‖ ≤ MQ') →
              (∀ i' : ℕ, 1 ≤ i' → i' ≤ m' → ‖iteratedFDeriv ℝ i' φ x‖ ≤ MD' ^ i') →
              ‖Work.Diff.STE.pdVec m' β (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ((∑ a : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  P a z * Q a (φ z) : ℝ) : ℂ)) x‖
                ≤ C * MP' * (1 + MD') ^ m' * MQ') :=
          fun m' => pdVec_ofReal_sum_mul_comp_le_aux (n := Module.finrank ℝ E)
            (κ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) m'
        choose Cm hCmnn hCmprop using hCml
        set CC : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun m' : Fin (k + 2) =>
            Cm m'.val * MP * (1 + MD) ^ m'.val * K) with hCC
        refine ⟨CC, ?_, U, hUmem, ?_⟩
        · rw [hCC]
          refine le_trans ?_ (Finset.le_sup'
            (fun m' : Fin (k + 2) => Cm m'.val * MP * (1 + MD) ^ m'.val * K)
            (Finset.mem_univ (⟨0, by omega⟩ : Fin (k + 2))))
          exact mul_nonneg (mul_nonneg (mul_nonneg (hCmnn 0) hMPnn)
            (pow_nonneg (by linarith) _)) hK.le
        · intro y hy h hh m hm β
          have hyGs : y ∈ Gs := hy.1.1
          have hQon : ∀ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ContDiffOn ℝ (⊤ : ℕ∞) (fun u => D.mat i h q.1 q.2 u) t := fun q => fun u hu =>
            (mat_contDiffAt_of_chartData (I := I) (M := M) D h hh.2.1 i q.1 q.2 u
              (interior_subset hu)).mono (Set.subset_univ t)
          have hPjet : ∀ (q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (m' : ℕ),
              m' ≤ k + 1 → ∀ γ : Fin m' → Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m' γ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((A q.1 y * B q.2 y : ℝ) : ℂ)) y‖ ≤ MP := by
            intro q m' hm' γ
            have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (A q.1 * B q.2) y :=
              ((noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j c q.1 hyGs.1).mul
                (noT2_contDiffAt_pairing_pt (I := I) (M := M) D i j j d q.2 hyGs.1))
            rw [Work.Diff.STE.B3.pdVec_ofReal_eq
              (f := fun y : Fin (Module.finrank ℝ E) → ℝ => A q.1 y * B q.2 y) hsm m' γ,
              Complex.norm_real]
            have hyb : ‖iteratedFDeriv ℝ m' (A q.1 * B q.2) y‖
                < ‖iteratedFDeriv ℝ m' (A q.1 * B q.2) z‖ + 1 :=
              (Set.mem_iInter.mp (Set.mem_iInter.mp hy.1.2 (⟨m', by omega⟩ : Fin (k + 2)))) q
            calc ‖iteratedFDeriv ℝ m' (A q.1 * B q.2) y (fun j => Pi.single (γ j) (1 : ℝ))‖
                ≤ ‖iteratedFDeriv ℝ m' (A q.1 * B q.2) y‖ := eval_basis_le y γ
              _ ≤ ‖iteratedFDeriv ℝ m' (A q.1 * B q.2) z‖ + 1 := le_of_lt hyb
              _ ≤ MP := by
                  rw [hMP]
                  refine le_trans ?_ (le_max_right _ _)
                  refine le_trans (Finset.le_sup' (fun i' : Fin (k + 2) =>
                      ‖iteratedFDeriv ℝ i'.val (A q.1 * B q.2) z‖ + 1)
                    (Finset.mem_univ (⟨m', by omega⟩ : Fin (k + 2)))) ?_
                  exact Finset.le_sup' (fun q' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
                      Finset.univ.sup' Finset.univ_nonempty (fun i' : Fin (k + 2) =>
                        ‖iteratedFDeriv ℝ i'.val (A q'.1 * B q'.2) z‖ + 1))
                    (Finset.mem_univ q)
          have hQjet : ∀ (q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (m' : ℕ),
              m' ≤ k + 1 → ∀ γ : Fin m' → Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m' γ (fun u : Fin (Module.finrank ℝ E) → ℝ =>
                ((D.mat i h q.1 q.2 u : ℝ) : ℂ)) (T y)‖ ≤ K :=
            fun q m' hm' γ => hh.2.2 i q.1 q.2 m' hm' γ (T y) (le_of_lt hyGs.2)
          have hTjet : ∀ (i' : ℕ), 1 ≤ i' → i' ≤ k + 1 →
              ‖iteratedFDeriv ℝ i' T y‖ ≤ MD ^ i' := by
            intro i' h1 h2
            have hyb : ‖iteratedFDeriv ℝ i' T y‖ < ‖iteratedFDeriv ℝ i' T z‖ + 1 :=
              Set.mem_iInter.mp hy.2 (⟨i', by omega⟩ : Fin (k + 2))
            calc ‖iteratedFDeriv ℝ i' T y‖ ≤ ‖iteratedFDeriv ℝ i' T z‖ + 1 := le_of_lt hyb
              _ ≤ MD := by
                  rw [hMD]
                  refine le_trans ?_ (le_max_right _ _)
                  exact Finset.le_sup' (fun i'' : Fin (k + 2) => ‖iteratedFDeriv ℝ i''.val T z‖ + 1)
                    (Finset.mem_univ (⟨i', by omega⟩ : Fin (k + 2)))
              _ ≤ MD ^ i' := le_self_pow₀ hMD1 (by omega)
          have hcomp := hCmprop m Gs t hGsopen htopen
            (fun q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
              fun w => A q.1 w * B q.2 w)
            (fun q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
              fun u => D.mat i h q.1 q.2 u)
            T y β MP MD K hMPnn hMDnn hK.le hy.1.1 hst
            (fun q => (hAsm q.1).mul (hBsm q.2))
            hQon
            hTsm
            (fun q m' hm' γ => hPjet q m' (by omega) γ)
            (fun q m' hm' γ => hQjet q m' (by omega) γ)
            (fun i' h1 h2 => hTjet i' h1 (by omega))
          have heqOn : Set.EqOn
              (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat j h c d y : ℝ) : ℂ))
              (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  (A q.1 y * B q.2 y) * D.mat i h q.1 q.2 (T y) : ℝ) : ℂ)) Gs := by
            intro w hw
            have hexp := Work.Diff.STE.B3.MatGlob.mat_expansion (I := I) (M := M) D i j h c d w
              hw.1.2.1 (le_of_lt hw.2)
            have hreal : D.mat j h c d w
                = ∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    (A q.1 w * B q.2 w) * D.mat i h q.1 q.2 (T w) := by
              rw [hexp, Fintype.sum_prod_type]
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
              simp only [hA, hB, hTapply w]
            show ((D.mat j h c d w : ℝ) : ℂ)
                = ((∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    (A q.1 w * B q.2 w) * D.mat i h q.1 q.2 (T w) : ℝ) : ℂ)
            rw [hreal]
          have hfsm : ContDiffAt ℝ (⊤ : ℕ∞)
              (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat j h c d y : ℝ) : ℂ)) y :=
            (Complex.ofRealCLM.contDiff.contDiffAt).comp y
              (mat_contDiffAt_of_chartData (I := I) (M := M) D h hh.2.1 j c d y
                (interior_subset hyGs.1.1))
          have hgsm : ContDiffAt ℝ (⊤ : ℕ∞)
              (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  (A q.1 y * B q.2 y) * D.mat i h q.1 q.2 (T y) : ℝ) : ℂ)) y :=
            (Complex.ofRealCLM.contDiff.contDiffAt).comp y
              (ContDiffAt.sum (s := Finset.univ) fun q _ =>
                (((hAsm q.1).contDiffAt (hGsopen.mem_nhds hyGs)).mul
                  ((hBsm q.2).contDiffAt (hGsopen.mem_nhds hyGs))).mul
                  (((hQon q).contDiffAt (htopen.mem_nhds (hst hyGs))).comp y
                    (hTsm.contDiffAt (hGsopen.mem_nhds hyGs))))
          rw [pdVec_congr_of_eqOn hGsopen hyGs hfsm hgsm heqOn m β]
          exact le_trans hcomp (Finset.le_sup'
            (fun m' : Fin (k + 2) => Cm m'.val * MP * (1 + MD) ^ m'.val * K)
            (Finset.mem_univ (⟨m, by omega⟩ : Fin (k + 2))))
      -- ## the compactness step, chart by chart
      have hCj : ∀ j : ι₀, ∃ Cj : ℝ, 0 ≤ Cj ∧
          ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
            (hz : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ))
            (c d : Fin (Module.finrank ℝ E)) (h : Work.Diff.STE.Bil (I := I) (M := M))
            (hh : PackJet (I := I) (M := M) D k K h) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)),
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat j h c d y : ℝ) : ℂ)) z‖ ≤ Cj := by
        intro j
        set f : ({h : Work.Diff.STE.Bil (I := I) (M := M) //
              PackJet (I := I) (M := M) D k K h} ×
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
            (Σ m' : Fin (k + 2), Fin m'.val → Fin (Module.finrank ℝ E))) →
            (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
          fun i y => ‖Work.Diff.STE.pdVec i.2.2.1.val i.2.2.2
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat j i.1.1 i.2.1.1 i.2.1.2 y : ℝ) : ℂ)) y‖ with hfdef
        have hloc' : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
              (2 * D.σ j + δ),
            ∃ C : ℝ, ∃ u ∈ nhds z, ∀ y ∈ u,
              ∀ i : ({h : Work.Diff.STE.Bil (I := I) (M := M) //
                  PackJet (I := I) (M := M) D k K h} ×
                (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
                (Σ m' : Fin (k + 2), Fin m'.val → Fin (Module.finrank ℝ E))),
              |f i y| ≤ C := by
          intro z hzmem
          have hz : ‖z‖ ≤ 2 * D.σ j + δ := by
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hzmem
            exact hzmem
          choose Cp hCpnn Cup hCupmem hCup using fun p : Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E) => hloc j z hz p.1 p.2
          refine ⟨Finset.univ.sup' Finset.univ_nonempty Cp, ⋂ p, Cup p,
            Filter.iInter_mem.mpr hCupmem, ?_⟩
          intro y hy i
          have hyp : y ∈ Cup i.2.1 := Set.mem_iInter.mp hy i.2.1
          have hbound := hCup i.2.1 y hyp i.1.1 i.1.2 i.2.2.1.val
            (Nat.lt_succ_iff.mp i.2.2.1.isLt) i.2.2.2
          refine le_trans ?_ (Finset.le_sup' Cp (Finset.mem_univ i.2.1))
          rw [abs_of_nonneg (show (0 : ℝ) ≤ f i y from by rw [hfdef]; exact norm_nonneg _)]
          exact hbound
        obtain ⟨Cj, hCjnn, hCjspec⟩ := Work.Diff.STE.B3.MatGlob.isCompact_uniform_bound
          (X := Fin (Module.finrank ℝ E) → ℝ)
          (ι := ({h : Work.Diff.STE.Bil (I := I) (M := M) //
              PackJet (I := I) (M := M) D k K h} ×
            (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
            (Σ m' : Fin (k + 2), Fin m'.val → Fin (Module.finrank ℝ E))))
          (f := f) (isCompact_closedBall _ _) hloc'
        refine ⟨Cj, hCjnn, ?_⟩
        intro z hzmem c d h hh m hm β
        have hspec := hCjspec (⟨h, hh⟩, (c, d), Sigma.mk ⟨m, by omega⟩ β) z hzmem
        have hfval : f (⟨h, hh⟩, (c, d), Sigma.mk ⟨m, by omega⟩ β) z
            = ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat j h c d y : ℝ) : ℂ)) z‖ := by
          simp only [hfdef]
        rw [hfval] at hspec
        exact le_trans (le_abs_self _) hspec
      choose Cj hCjnn hCjspec using hCj
      refine ⟨δ, Finset.univ.sup' Finset.univ_nonempty Cj, hδpos, ?_, ?_⟩
      · exact le_trans (hCjnn (Classical.arbitrary ι₀)) (Finset.le_sup' Cj (Finset.mem_univ _))
      · intro h hsym hsmooth hjet j c d m hm β z hz
        have hz' : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz
        exact le_trans (hCjspec j z hz' c d h ⟨hsym, hsmooth, hjet⟩ m hm β)
          (Finset.le_sup' Cj (Finset.mem_univ j))
  · refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro h hsym hsmooth hjet j c d m hm β z hz
    exact (hι ⟨j⟩).elim

end Work.Diff.STE.B3
