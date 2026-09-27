import Mathlib
import Submission.Work.Isotopy.Smooth
import Submission.Work.Embedding.Proper
-- TEMPORARY (development only): the three lemmas are being proved by colleagues in parallel
import Submission.Work.Isotopy.exists_family_retraction
import Submission.Work.Isotopy.exists_partition_of_unity_trail
import Submission.Work.Isotopy.exists_estimate_small

/-!
# The smooth isotopy extension theorem with compact support

This file proves `Work.Isotopy.exists_smoothAmbientIsotopy_extending`: a smooth family of smooth
embeddings of a compact manifold into `ℝ^N`, starting at a fixed smooth embedding `e`, stationary
in time outside `[0,1]` and equal to `e` outside a compact set `K`, is the restriction to `e '' univ`
of a smooth ambient isotopy of `ℝ^N` supported in a bounded open neighbourhood of `range e ∪ K`.

The proof has three ingredients, provided by the three auxiliary files imported above:

* `Work.Isotopy.exists_family_retraction`: parametrised local left inverses (retractions) of a
  smooth family of injective immersions of a compact manifold;
* `Work.Isotopy.exists_partition_of_unity_trail`: a smooth partition of unity subordinate to the
  resulting box cover and summing to one on the "trail" of the family;
* `Work.Isotopy.exists_estimate_small`: the resulting `z`-derivative estimate.

The isotopy itself is built as a *finite composition* of small pieces.  Writing `Φ s := F s` for the
family, choose a smooth *bounded* reparametrisation `c = phaseTop` of the time axis with
`F (c t) = F t`, and phases `θ i t = (min i k / k) * c t`.  Each piece is
`z ↦ z + ∑_j ψ_j (θ i t) z • (F (θ (i+1) t) (ρ_j (θ i t) z) - F (θ i t) (ρ_j (θ i t) z))`,
a small perturbation of the identity which maps `F (θ i t) x` to `F (θ (i+1) t) x`.  The composition
of the `k` pieces therefore maps `e x = F 0 x` to `F (c t) x = F t x`, and is globally smooth in
`(t, z)`, fixes everything outside a bounded neighbourhood of the trail, and is a self-embedding at
every time.
-/

namespace Work.Isotopy

open scoped Manifold ContDiff
open Topology Set Function

variable {N : ℕ}

/-- The identity smooth ambient isotopy (all time slices are the identity). -/
noncomputable def SmoothAmbientIsotopy.refl (N : ℕ) : SmoothAmbientIsotopy N where
  toFun := fun _ (x : EuclideanSpace ℝ (Fin N)) => x
  contMDiff_uncurry := by
    have h : Function.uncurry (fun (_ : ℝ) (x : EuclideanSpace ℝ (Fin N)) => x) =
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => p.2) := rfl
    rw [h]
    exact contMDiff_snd
  isEmbedding_apply := fun _ => IsEmbedding.id
  map_zero := rfl

@[simp]
theorem SmoothAmbientIsotopy.refl_apply (N : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    (SmoothAmbientIsotopy.refl N) t x = x := rfl

theorem contMDiff_prod_iff_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × EuclideanSpace ℝ (Fin N) → F) :
    (ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) 𝓘(ℝ, F) ∞ f ↔ ContDiff ℝ ∞ f) := by
  have h1 : (𝓘(ℝ, ℝ)).prod (𝓡 N) = 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin N)) := by
    rw [modelWithCornersSelf_prod]
  rw [h1]
  rw [show prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N)) =
      chartedSpaceSelf (ℝ × EuclideanSpace ℝ (Fin N)) from chartedSpaceSelf_prod]
  exact contMDiff_iff_contDiff

/-- A smooth "clamped identity": it is the identity on `[-2,2]`, takes values in `[-3,3]`, is
nonpositive on `(-∞,0]` and at least `1` on `[1,∞)`.  It is used to reparametrise the time axis of
an isotopy that is stationary outside `[0,1]` by a *bounded* function. -/
noncomputable def phaseTop : ℝ → ℝ :=
  fun t => t - (t - 1) * Real.smoothTransition (t - 2) - (t + 1) * Real.smoothTransition (-t - 2)

theorem phaseTop_contDiff : ContDiff ℝ ∞ phaseTop := by
  unfold phaseTop
  have h1 : ContDiff ℝ ∞ fun t : ℝ => t - 2 := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ ∞ fun t : ℝ => -t - 2 := contDiff_id.neg.sub contDiff_const
  exact (contDiff_id.sub ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp h1))).sub
    ((contDiff_id.add contDiff_const).mul (Real.smoothTransition.contDiff.comp h2))

theorem phaseTop_mem (t : ℝ) : phaseTop t ∈ Icc (-3 : ℝ) 3 := by
  have hγ0 : 0 ≤ Real.smoothTransition (t - 2) := Real.smoothTransition.nonneg _
  have hγ1 : Real.smoothTransition (t - 2) ≤ 1 := Real.smoothTransition.le_one _
  have hδ0 : 0 ≤ Real.smoothTransition (-t - 2) := Real.smoothTransition.nonneg _
  have hδ1 : Real.smoothTransition (-t - 2) ≤ 1 := Real.smoothTransition.le_one _
  rcases le_or_gt t (-3) with h | h
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2 : Real.smoothTransition (-t - 2) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    rw [phaseTop, h1, h2]
    constructor <;> norm_num
  rcases le_or_gt t (-2) with h2' | h2'
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have e1 : (t + 1) * (1 - Real.smoothTransition (-t - 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ -(t + 1) * Real.smoothTransition (-t - 2) :=
      mul_nonneg (by linarith) hδ0
    rw [phaseTop, h1]
    constructor
    · nlinarith [e2]
    · nlinarith [e1]
  rcases le_or_gt t 2 with h3 | h3
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2 : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [phaseTop, h1, h2]
    constructor <;> simp only [mul_zero, sub_zero] <;> linarith
  rcases le_or_gt t 3 with h4 | h4
  · have h2 : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have e1 : (t - 1) * (1 - Real.smoothTransition (t - 2)) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ (t - 1) * Real.smoothTransition (t - 2) := mul_nonneg (by linarith) hγ0
    rw [phaseTop, h2]
    constructor
    · nlinarith [e2]
    · nlinarith [e1]
  · have h1 : Real.smoothTransition (t - 2) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have h2 : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [phaseTop, h1, h2]
    constructor <;> norm_num

theorem phaseTop_of_abs_le {t : ℝ} (h : |t| ≤ 2) : phaseTop t = t := by
  have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by
    rw [abs_le] at h; linarith [h.2])
  have h2 : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by
    rw [abs_le] at h; linarith [h.1])
  rw [phaseTop, h1, h2]; ring

theorem phaseTop_nonpos_of_nonpos {t : ℝ} (h : t ≤ 0) : phaseTop t ≤ 0 := by
  have hγ0 : 0 ≤ Real.smoothTransition (t - 2) := Real.smoothTransition.nonneg _
  have hδ0 : 0 ≤ Real.smoothTransition (-t - 2) := Real.smoothTransition.nonneg _
  rcases le_or_gt t (-2) with h2 | h2
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have e1 : (t + 1) * (1 - Real.smoothTransition (-t - 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [Real.smoothTransition.le_one (-t - 2)])
    rw [phaseTop, h1]
    nlinarith [e1]
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2' : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [phaseTop, h1, h2']; simpa using h

theorem phaseTop_one_le {t : ℝ} (h : 1 ≤ t) : 1 ≤ phaseTop t := by
  have hγ0 : 0 ≤ Real.smoothTransition (t - 2) := Real.smoothTransition.nonneg _
  have hγ1 : Real.smoothTransition (t - 2) ≤ 1 := Real.smoothTransition.le_one _
  rcases le_or_gt t 2 with h2 | h2
  · have h1 : Real.smoothTransition (t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2' : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [phaseTop, h1, h2']; simpa using h
  · have h2' : Real.smoothTransition (-t - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have e1 : (t - 1) * (1 - Real.smoothTransition (t - 2)) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    rw [phaseTop, h2']
    nlinarith [e1]



/-- The phase functions used to distribute the motion of the isotopy over `k` small steps:
`phaseK k i t = (min i k / k) * phaseTop t`. -/
noncomputable def phaseK (k : ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) * phaseTop t

theorem phaseK_apply (k i : ℕ) (t : ℝ) :
    phaseK k i t = ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) * phaseTop t := rfl

theorem phaseK_contDiff (k i : ℕ) : ContDiff ℝ ∞ (phaseK k i) := by
  have h : phaseK k i = fun t : ℝ => (((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ)) * phaseTop t := by
    funext t; rw [phaseK_apply]
  rw [h]
  exact contDiff_const.mul phaseTop_contDiff

theorem phaseK_k {k : ℕ} (hk : (0 : ℝ) < (k : ℝ)) (t : ℝ) : phaseK k k t = phaseTop t := by
  rw [phaseK_apply, Nat.min_self, div_self hk.ne', one_mul]

theorem phaseK_zero (k : ℕ) (t : ℝ) : phaseK k 0 t = 0 := by
  rw [phaseK_apply, Nat.zero_min, Nat.cast_zero, zero_div, zero_mul]

theorem phaseK_diff (k i : ℕ) (t : ℝ) :
    phaseK k (i + 1) t - phaseK k i t =
      ((min (i + 1) k : ℕ) : ℝ) / ((k : ℕ) : ℝ) * phaseTop t -
        ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) * phaseTop t := rfl

theorem phaseK_step (k i : ℕ) (t : ℝ) :
    phaseK k (i + 1) t - phaseK k i t =
      (((min (i + 1) k : ℕ) : ℝ) - ((min i k : ℕ) : ℝ)) / ((k : ℕ) : ℝ) * phaseTop t := by
  rw [phaseK_diff]; ring

/-! ## The isotopy extension theorem -/

theorem exists_smoothAmbientIsotopy_extending {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hemb : IsEmbedding e) (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x))
    (F : ℝ → M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 N) ∞ (Function.uncurry F))
    (hFemb : ∀ t, IsEmbedding (F t))
    (hFimm : ∀ t x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) (F t) x))
    (hF0 : F 0 = e)
    (hFstat : ∀ t x, (t ≤ 0 ∨ 1 ≤ t) → F t x = e x)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hK : IsCompact K)
    (hFsupp : ∀ t x, e x ∉ K → F t x = e x) :
    ∃ Ψ : Work.Isotopy.SmoothAmbientIsotopy N,
      (∀ t x, Ψ t (e x) = F t x) ∧
      ∃ U : Set (EuclideanSpace ℝ (Fin N)), IsOpen U ∧ IsCompact (closure U) ∧
        Set.range e ⊆ U ∧ K ⊆ U ∧ ∀ t y, y ∉ U → Ψ t y = y := by
  -- STEP 1: parametrised local retractions of the family `F`
  obtain ⟨ι, hι, O, B, ρ, hO, hB, hBd, hρ, hρcorr, hcover⟩ :=
    exists_family_retraction F hF hFimm (fun s => (hFemb s).injective) (-3) 3 (by norm_num)
  haveI : Fintype ι := hι
  -- STEP 2: a partition of unity supported on the boxes, summing to one on the trail
  obtain ⟨ψ, hψ, hψnn, hψsupp, hψsum⟩ :=
    exists_partition_of_unity_trail (n := n) (N := N) (Φ := F) hO hB hF.continuous (-3) 3 hcover
  -- STEP 3: uniform smallness of the derivative of the phase-corrected displacement
  obtain ⟨η, hηpos, hest⟩ :=
    exists_estimate_small (N := N) (Φ := F) hF ρ hρ ψ hψ hBd
      (fun j s z h => (hψsupp j s z h).2) (-3) 3 (by norm_num)
  -- STEP 4: the bounded reparametrisation of time
  have hcF : ∀ t, F (phaseTop t) = F t := by
    intro t
    funext x
    rcases le_or_gt t (-2) with ht | ht
    · have h1 : phaseTop t ≤ 0 := phaseTop_nonpos_of_nonpos (t := t) (by linarith)
      rw [hFstat (phaseTop t) x (Or.inl h1), hFstat t x (Or.inl (by linarith))]
    rcases le_or_gt t 2 with ht2 | ht2
    · have h1 : phaseTop t = t := phaseTop_of_abs_le (t := t) (by rw [abs_le]; exact ⟨by linarith, ht2⟩)
      rw [h1]
    · have h1 : 1 ≤ phaseTop t := phaseTop_one_le (t := t) (by linarith)
      rw [hFstat (phaseTop t) x (Or.inr h1), hFstat t x (Or.inr (by linarith))]
  -- STEP 5: number of pieces
  obtain ⟨k, hk1, hkη⟩ : ∃ k : ℕ, 1 ≤ k ∧ (3 : ℝ) / k ≤ η := by
    obtain ⟨k, hk⟩ := exists_nat_gt (3 / η)
    have hk3 : (0 : ℝ) < 3 / η := by positivity
    have hk0 : (0 : ℕ) < k := by exact_mod_cast (lt_trans hk3 hk : (0 : ℝ) < (k : ℝ))
    refine ⟨k, hk0, ?_⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    rw [div_le_iff₀ hkpos]
    have h : 3 / η < (k : ℝ) := hk
    rw [div_lt_iff₀ hηpos] at h
    linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  -- STEP 6: the phases
  let θ : ℕ → ℝ → ℝ := phaseK k
  have hθ_apply : ∀ i t, θ i t = ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) * phaseTop t :=
    fun i t => phaseK_apply k i t
  have hθ_smooth : ∀ i, ContDiff ℝ ∞ (θ i) := fun i => phaseK_contDiff k i
  have hθmem : ∀ i t, θ i t ∈ Icc (-3 : ℝ) 3 := by
    intro i t
    rw [hθ_apply i t]
    have h1 : (0 : ℝ) ≤ ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) := by positivity
    have h2 : ((min i k : ℕ) : ℝ) / ((k : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hkpos]
      exact_mod_cast Nat.min_le_right i k
    have h3 := phaseTop_mem t
    constructor <;> nlinarith [h1, h2, h3.1, h3.2]
  have hθk : ∀ t, θ k t = phaseTop t := fun t => phaseK_k hkpos t
  have hθgap : ∀ i t, |θ (i + 1) t - θ i t| ≤ η := by
    intro i t
    have hle : min i k ≤ min (i + 1) k := min_le_min_right k (Nat.le_succ i)
    have hlt : min (i + 1) k ≤ min i k + 1 := by omega
    have hlow : 0 ≤ ((min (i + 1) k : ℕ) : ℝ) - ((min i k : ℕ) : ℝ) := by
      have : ((min i k : ℕ) : ℝ) ≤ ((min (i + 1) k : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    have hup : ((min (i + 1) k : ℕ) : ℝ) - ((min i k : ℕ) : ℝ) ≤ 1 := by
      have h2 : ((min (i + 1) k : ℕ) : ℝ) ≤ ((min i k : ℕ) : ℝ) + 1 := by
        calc ((min (i + 1) k : ℕ) : ℝ) ≤ ((min i k + 1 : ℕ) : ℝ) := by exact_mod_cast hlt
          _ = ((min i k : ℕ) : ℝ) + 1 := by push_cast; ring
      linarith
    have hdiff : θ (i + 1) t - θ i t =
        (((min (i + 1) k : ℕ) : ℝ) - ((min i k : ℕ) : ℝ)) / ((k : ℕ) : ℝ) * phaseTop t := by
      rw [show θ (i + 1) t = phaseK k (i + 1) t from rfl, show θ i t = phaseK k i t from rfl]
      exact phaseK_step k i t
    rw [hdiff]
    simp only [abs_mul, abs_div, abs_of_nonneg hlow, abs_of_pos hkpos]
    have hPT : |phaseTop t| ≤ 3 := by
      have h3 := phaseTop_mem t
      exact abs_le.mpr ⟨h3.1, h3.2⟩
    have hkey : (((min (i + 1) k : ℕ) : ℝ) - ((min i k : ℕ) : ℝ)) * |phaseTop t| ≤ 3 := by
      have h := mul_le_mul hup hPT (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have h3 : (3 : ℝ) ≤ η * (k : ℝ) := (div_le_iff₀ hkpos).mp hkη
    rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
    linarith [hkey]
  -- STEP 7: the displacement fields of the individual pieces
  let E : ℕ → ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun i t z =>
    ∑ j, ψ j (θ i t) z • (F (θ (i + 1) t) (ρ j (θ i t) z) - F (θ i t) (ρ j (θ i t) z))
  have hEsmooth : ∀ i, ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => E i p.1 p.2) := by
    intro i
    have hθi : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => θ i p.1) :=
      (hθ_smooth i).contMDiff.comp contMDiff_fst
    have hθi1 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => θ (i + 1) p.1) :=
      (hθ_smooth (i + 1)).contMDiff.comp contMDiff_fst
    have hpair : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (θ i p.1, p.2)) :=
      ContMDiff.prodMk hθi contMDiff_snd
    refine ContMDiff.sum (t := Finset.univ) (fun j _ => ?_)
    have hsc : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => ψ j (θ i p.1) p.2) :=
      ((contMDiff_prod_iff_contDiff (Function.uncurry (ψ j))).mpr (hψ j)).comp hpair
    have hρc : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 n) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => ρ j (θ i p.1) p.2) :=
      (hρ j).comp hpair
    have ht1 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => F (θ (i + 1) p.1) (ρ j (θ i p.1) p.2)) :=
      hF.comp (ContMDiff.prodMk hθi1 hρc)
    have ht2 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => F (θ i p.1) (ρ j (θ i p.1) p.2)) :=
      hF.comp (ContMDiff.prodMk hθi hρc)
    exact hsc.smul (ht1.sub ht2)
  have hEbound : ∀ i t, ∀ y : EuclideanSpace ℝ (Fin N), ‖fderiv ℝ (E i t) y‖ ≤ 1 / 2 := by
    intro i t y
    exact hest (θ i t) (hθmem i t) (θ (i + 1) t) (hθmem (i + 1) t) (hθgap i t) y
  have hEslice : ∀ i t, ContDiff ℝ ∞ (E i t) := by
    intro i t
    have hf : ContMDiff (𝓡 N) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
        (fun z : EuclideanSpace ℝ (Fin N) => ((t : ℝ), z)) :=
      ContMDiff.prodMk (contMDiff_const) contMDiff_id
    exact ((hEsmooth i).comp hf).contDiff
  have hEmble : ∀ i t, IsEmbedding (fun z : EuclideanSpace ℝ (Fin N) => z + E i t z) := by
    intro i t
    have hdiff : Differentiable ℝ (E i t) := (hEslice i t).differentiable (by simp)
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin N) => z + E i t z) :=
      continuous_id.add (hEslice i t).continuous
    refine AntilipschitzWith.isEmbedding (K := 2) ?_ hcont
    refine AntilipschitzWith.of_le_mul_dist (K := 2) ?_
    intro z z'
    have hlip : ‖E i t z - E i t z'‖ ≤ (1 / 2) * ‖z - z'‖ := by
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := E i t) (C := 1 / 2)
        (s := Set.univ) (x := z') (y := z) (fun u _ => hdiff.differentiableAt)
        (fun u _ => hEbound i t u) convex_univ (mem_univ _) (mem_univ _)
      simpa using h
    have h2 : ‖z - z'‖ ≤ ‖(z + E i t z) - (z' + E i t z')‖ + ‖E i t z - E i t z'‖ := by
      have h3 : z - z' = ((z + E i t z) - (z' + E i t z')) - (E i t z - E i t z') := by abel
      calc ‖z - z'‖ = ‖((z + E i t z) - (z' + E i t z')) - (E i t z - E i t z')‖ := by rw [h3]
        _ ≤ ‖(z + E i t z) - (z' + E i t z')‖ + ‖E i t z - E i t z'‖ := norm_sub_le _ _
    have hgoal : ‖z - z'‖ ≤ 2 * ‖(z + E i t z) - (z' + E i t z')‖ := by linarith
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using hgoal
  -- STEP 8: the individual pieces, and their composition
  let piece : ℕ → SmoothAmbientIsotopy N := fun i =>
    { toFun := fun t z => z + E i t z
      contMDiff_uncurry := by
        have h : Function.uncurry (fun t (z : EuclideanSpace ℝ (Fin N)) => z + E i t z) =
            (fun p : ℝ × EuclideanSpace ℝ (Fin N) => p.2 + E i p.1 p.2) := rfl
        rw [h]
        exact contMDiff_snd.add (hEsmooth i)
      isEmbedding_apply := fun t => hEmble i t
      map_zero := by
        funext z
        have hPT0 : phaseTop 0 = 0 := phaseTop_of_abs_le (t := 0) (by norm_num)
        have h1 : θ i 0 = 0 := by
          rw [hθ_apply i 0, hPT0, mul_zero]
        have h2 : θ (i + 1) 0 = 0 := by
          rw [hθ_apply (i + 1) 0, hPT0, mul_zero]
        have h3 : E i 0 z = 0 := by
          simp only [E, h1, h2, sub_self, smul_zero, Finset.sum_const_zero]
        simp [h3] }
  let P : ℕ → SmoothAmbientIsotopy N :=
    Nat.rec (SmoothAmbientIsotopy.refl N) (fun i acc => (piece i).comp acc)
  have hPzero : P 0 = SmoothAmbientIsotopy.refl N :=
    Nat.rec_zero (SmoothAmbientIsotopy.refl N) (fun i acc => (piece i).comp acc)
  have hPsucc : ∀ i, P (i + 1) = (piece i).comp (P i) := fun i => rfl
  -- the telescoping property of the pieces
  have hconstr : ∀ i t x, E i t (F (θ i t) x) = F (θ (i + 1) t) x - F (θ i t) x := by
    intro i t x
    have hsum : ∑ j, ψ j (θ i t) (F (θ i t) x) = 1 := hψsum (θ i t) (hθmem i t) x
    have hterm : ∀ j, ψ j (θ i t) (F (θ i t) x) •
        (F (θ (i + 1) t) (ρ j (θ i t) (F (θ i t) x)) -
          F (θ i t) (ρ j (θ i t) (F (θ i t) x))) =
        ψ j (θ i t) (F (θ i t) x) • (F (θ (i + 1) t) x - F (θ i t) x) := by
      intro j
      by_cases h : ψ j (θ i t) (F (θ i t) x) = 0
      · rw [h, zero_smul, zero_smul]
      · obtain ⟨h1, h2⟩ := hψsupp j (θ i t) (F (θ i t) x) h
        rw [hρcorr j (θ i t) x h1 h2]
    show (∑ j, ψ j (θ i t) (F (θ i t) x) •
        (F (θ (i + 1) t) (ρ j (θ i t) (F (θ i t) x)) -
          F (θ i t) (ρ j (θ i t) (F (θ i t) x)))) = _
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_smul, hsum, one_smul]
  have hP : ∀ i, ∀ t x, P i t (e x) = F (θ i t) x := by
    intro i
    induction i with
    | zero =>
      intro t x
      have h0 : θ 0 t = 0 := by
        rw [show θ 0 t = phaseK k 0 t from rfl]
        exact phaseK_zero k t
      rw [hPzero, h0, hF0]
      simp
    | succ i ih =>
      intro t x
      rw [hPsucc i, SmoothAmbientIsotopy.comp_apply, ih t x]
      show F (θ i t) x + E i t (F (θ i t) x) = F (θ (i + 1) t) x
      rw [hconstr i t x]
      abel
  -- the pieces fix everything outside the union of the boxes
  have hPfix : ∀ i t y, y ∉ ⋃ j, B j → P i t y = y := by
    intro i
    induction i with
    | zero => intro t y _; rw [hPzero]; simp
    | succ i ih =>
      intro t y hy
      rw [hPsucc i, SmoothAmbientIsotopy.comp_apply, ih t y hy]
      have hE0 : E i t y = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have h : ψ j (θ i t) y = 0 := by
          by_contra h'
          exact hy (Set.mem_iUnion.mpr ⟨j, (hψsupp j (θ i t) y h').2⟩)
        rw [h, zero_smul]
      show y + E i t y = y
      rw [hE0, add_zero]
  -- STEP 9: the conclusion
  refine ⟨P k, ?_, ?_⟩
  · intro t x
    rw [hP k t x, hθk t, hcF t]
  · obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, (⋃ j, B j) ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R₁ := by
      have hb : Bornology.IsBounded (⋃ j, B j) :=
        (Bornology.isBounded_iUnion).mpr (fun j => hBd j)
      exact hb.subset_closedBall 0
    obtain ⟨R, hR⟩ : ∃ R : ℝ, Set.range e ∪ K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R := by
      have hb : Bornology.IsBounded (Set.range e ∪ K) := by
        rw [show Set.range e = e '' (Set.univ : Set M) from Set.image_univ.symm]
        exact ((isCompact_univ.image he.continuous).isBounded).union hK.isBounded
      exact hb.subset_closedBall 0
    refine ⟨(⋃ j, B j) ∪ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (R + 1), ?_, ?_, ?_, ?_, ?_⟩
    · exact (isOpen_iUnion hB).union Metric.isOpen_ball
    · have hsub : closure ((⋃ j, B j) ∪ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (R + 1)) ⊆
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (max R₁ (R + 1)) := by
        apply closure_minimal _ Metric.isClosed_closedBall
        intro z hz
        rcases hz with hz | hz
        · exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₁ hz)
        · exact Metric.closedBall_subset_closedBall (le_max_right _ _)
            (Metric.ball_subset_closedBall hz)
      exact (isCompact_closedBall 0 (max R₁ (R + 1))).of_isClosed_subset isClosed_closure hsub
    · intro y hy
      exact Or.inr (Metric.closedBall_subset_ball (by linarith) (hR (Or.inl hy)))
    · intro y hy
      exact Or.inr (Metric.closedBall_subset_ball (by linarith) (hR (Or.inr hy)))
    · intro t y hy
      refine hPfix k t y (fun h => hy (Or.inl h))

end Work.Isotopy
