import Mathlib
import Submission.Work.HP.nonarch
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.ArchGlueV2
import Submission.Work.HP.eval_bounds
import Submission.Work.HP.slab_vol
import Submission.Work.HP.cone_scale
import Submission.Work.HP.tau_prop_scale
import Submission.Work.HP.lattice_toolsV2
import Submission.Work.HP.tau_lower_allV2
import Submission.Work.HP.vol_Bset
import Submission.Work.HP.Lset_zero
import Submission.Work.HP.boundary
import Submission.Work.HP.geom_tail
import Submission.Work.HP.tau_vol_leV2
import Submission.Work.HP.count_good_le
import Submission.Work.HP.count_small_leV2
import Submission.Work.HP.log_eventually
import Submission.Work.HP.count_good_le
import Submission.Work.HP.count_small_leV2
import Submission.Work.HP.geom_tail

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Classical Finset MvPolynomial MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Work.HP


/-! ## Glue for the final assembly -/

/-- The unit `rNorm`-ball has finite volume. -/
lemma volume_unit_ball_ne_top {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℝ) :
    volume {w : ι → ℝ | rNorm w ≤ r} ≠ ⊤ := by
  rcases le_total r 0 with hr | hr
  · have : {w : ι → ℝ | rNorm w ≤ r} ⊆ {w : ι → ℝ | w = 0} := by
      intro w hw
      refine funext fun i => ?_
      have h1 : |w i| ≤ rNorm w := abs_apply_le_rNorm w i
      have h2 : rNorm w ≤ r := hw
      have h3 : |w i| ≤ 0 := by linarith
      simpa using le_antisymm h3 (abs_nonneg _)
    have hle : volume {w : ι → ℝ | rNorm w ≤ r} ≤ 0 := by
      refine le_trans (measure_mono this) ?_
      have hset : {w : ι → ℝ | w = 0} = Set.univ.pi (fun _ : ι => ({0} : Set ℝ)) := by
        ext w; simp [funext_iff]
      rw [hset, MeasureTheory.volume_pi_pi]
      simp
    exact ne_top_of_le_ne_top ENNReal.zero_ne_top hle
  · have hbox : {w : ι → ℝ | rNorm w ≤ r} ⊆ Set.univ.pi (fun _ : ι => Set.Icc (-r) r) := by
      intro w hw i _
      have h1 : |w i| ≤ rNorm w := abs_apply_le_rNorm w i
      have h2 : rNorm w ≤ r := hw
      exact ⟨by linarith [neg_abs_le (w i)], by linarith [le_abs_self (w i)]⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono hbox)
    rw [MeasureTheory.volume_pi_pi]
    exact (ENNReal.prod_lt_top fun i _ => by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top).ne

/-- `τ(a;2γ) ≤ 2 τ(a;γ)`: the band for `2γ` is contained in the band for `γ`. -/
lemma tauArch_two_le (d n : ℕ) (a : Mon d n → ℝ) {γ : ℝ} (hγ : 0 < γ) :
    tauArch d n a (2 * γ) ≤ 2 * tauArch d n a γ := by
  have hmono : volume (band d n a (2 * γ)) ≤ volume (band d n a γ) :=
    measure_mono (band_anti a hγ (by linarith))
  have hfin : volume (band d n a γ) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_unit_ball_ne_top (ι := Fin (n + 1)) 1)
      (measure_mono (fun u hu => hu.1))
  have hle : (volume (band d n a (2 * γ))).toReal ≤ (volume (band d n a γ)).toReal :=
    ENNReal.toReal_mono hfin hmono
  rw [tauArch_eq, tauArch_eq]
  nlinarith [hle, hγ]



instance instNonemptyMon (d n : ℕ) : Nonempty (Mon d n) :=
  ⟨⟨fun i => if i = 0 then ⟨d, Nat.lt_succ_self d⟩ else 0, by
      have h : ∀ i : Fin (n + 1),
          (((if i = 0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0) : Fin (d + 1)) : ℕ)
            = if i = 0 then d else 0 := by
        intro i; by_cases hi : i = 0 <;> simp [hi]
      rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_eq']
      simp⟩⟩

/-- **Node N12 (`Work.HP.arch`) in a module that can be imported together with
`Submission.Work.HP.nonarch` (node N11).**  This is the *same statement* as `Work.HP.arch`
(`Submission/Work/HP/arch.lean`), placed in the new module `Submission.Work.HP.arch_v2` so that the
final assembly of `Work.HP.prop2` can use N11 and N12 in one environment.

Why a copy is needed: `Submission.Work.HP.arch` transitively imports `Submission.Work.HP.ArchGlue`
and `Submission.Work.HP.nonarch` transitively imports `Submission.Work.HP.MinkDefs`, and both of
those declare a result called `Work.HP.eNorm_nonneg` (with different signatures).  Lean rejects any
environment containing both, so the two nodes cannot be imported together as they stand.  (It was
checked that this is the *only* public name collision between the two closures.)

Intended route (a repackaging job, not new mathematics): copy the proof of `Work.HP.arch` into
`Submission/Work/HP/arch_v2.lean`, and for this copy replace the imports that reach
`Submission.Work.HP.ArchGlue` by renamed clones.  The affected modules (everything in the
transitive import closure of `arch` from which `ArchGlue` is reachable) are
`ArchGlue`, `count_small_le`, `small_union_vol`, `tau_lower_all`, `tau_meas_pos`, `tau_vol_le`,
`arch`.  Suggested recipe:
* create `Submission/Work/HP/ArchGlueV2.lean` = copy of `ArchGlue.lean` **without** the
  `eNorm_nonneg` result (it is unused by all the modules below, checked by grep);
* for each of `count_small_le`, `small_union_vol`, `tau_lower_all`, `tau_meas_pos`, `tau_vol_le`,
  create a `...V2` copy in which every import of an affected module is redirected to its `V2`
  version (e.g. `import Submission.Work.HP.ArchGlue` becomes
  `import Submission.Work.HP.ArchGlueV2`);
* create `Submission/Work/HP/arch_v2.lean` as the copy of `arch.lean` with the same redirections;
  its proof body needs no changes (no affected module mentions `eNorm_nonneg`).
Because none of the affected modules is imported by the transitive closure of `nonarch`, and
because the `V2` copies keep all their original declaration names, an environment that imports
`Submission.Work.HP.nonarch` and `Submission.Work.HP.arch_v2` is consistent.  Nothing else in the
workspace imports the `V2` modules, so nothing else is disturbed. -/
theorem arch_v3 (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => RealSol d n a ∧
          tauArch d n (toR a) (Real.log (A * φ)) < C / φ ^ ((1 : ℝ) / 6))
        ≤ K * A ^ NN d n / φ ^ (1 / (6 * (n : ℝ))) := by
  obtain ⟨hvalE, hgradE, hflipE, hglipE, htayE, hhom, hclose, hsol⟩ := eval_bounds d n hd hn
  obtain ⟨Cv, hCv, hval⟩ := hvalE
  obtain ⟨Cg, hCg, hgrad⟩ := hgradE
  obtain ⟨Cgl, hCgl, hgradlip⟩ := hglipE
  obtain ⟨Ct, hCt, htay⟩ := htayE
  obtain ⟨Ks, hKs, hslab⟩ := slab_vol d n hd hn
  obtain ⟨hcones, hunitne0, hunitnetop, hballcone⟩ := cone_scale d n
  obtain ⟨hpropp, hscalep, hIscalep⟩ := tau_prop_scale d n hd hn
  obtain ⟨hfin, hunitne0', hunitnetop', hballscale, hpack⟩ := lattice_tools d n hn
  obtain ⟨hgeom1, hgeom2⟩ := geom_tail
  have hunitpos : (0 : ℝ≥0∞) < volume {w : Mon d n → ℝ | rNorm w ≤ 1} :=
    pos_iff_ne_zero.mpr hunitne0'
  obtain ⟨Kt, hKt, hlow⟩ := tau_lower_all d n hd hn ⟨Cg, hCg, hgrad⟩ ⟨Ct, hCt, htay⟩
    ⟨hballscale, hunitpos⟩
  obtain ⟨Kb, hKb, hbvol⟩ := vol_Bset d n hd hn ⟨Ks, hKs, hslab⟩ ⟨Ct, hCt, htay⟩ hballscale
  have hL : volume (Lset d n) = 0 :=
    Lset_zero d n hd hn ⟨Ks, hKs, hslab⟩ ⟨Cgl, hCgl, hgradlip⟩ ⟨Ct, hCt, htay⟩ hballscale
  obtain ⟨Ku, hKu, hbnd⟩ := boundary d n hd hn ⟨Cg, hCg, hgrad⟩ ⟨Cgl, hCgl, hgradlip⟩
    ⟨Ct, hCt, htay⟩ ⟨Cv, hCv, hval⟩ hclose
  obtain ⟨Kτ, hKτ, hτvol⟩ :=
    tau_vol_le d n hd hn hCg hKt hKb hgrad hlow hbvol hL hgeom1 (hgeom2 Cg hCg) hunitnetop'
  set v : ℝ := (volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}).toReal with hv
  have hvpos : 0 < v := by
    rw [hv]
    have h1 : volume {w : Mon d n → ℝ | rNorm w ≤ (1 / 2 : ℝ)}
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1} := by
      simpa using hballscale (1 / 2) (0 : Mon d n → ℝ) (by norm_num)
    rw [h1]
    refine ENNReal.toReal_pos (mul_ne_zero (by simp) hunitne0') ?_
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hunitnetop'
  set Vu : ℝ := (volume {w : Mon d n → ℝ | rNorm w ≤ 1}).toReal with hVu
  have Vu_nonneg : 0 ≤ Vu := ENNReal.toReal_nonneg
  have hVu_pos : 0 < Vu := by
    rw [hVu]
    exact ENNReal.toReal_pos hunitne0' hunitnetop'
  -- the target constants
  set K' : ℝ := (12 * (Kτ * (4 : ℝ) ^ (1 / (n : ℝ))) + 2) / v with hK'
  have hK'pos : 0 < K' := by
    rw [hK']
    refine div_pos (by positivity) hvpos
  have hK'ge : 3 * Kτ * (4 : ℝ) ^ (1 / (n : ℝ)) / v ≤ K' := by
    rw [hK', le_div_iff₀ hvpos, div_mul_cancel₀ _ (ne_of_gt hvpos)]
    have h1 : 0 < Kτ * (4 : ℝ) ^ (1 / (n : ℝ)) := by positivity
    nlinarith
  refine ⟨K' * C ^ (1 / (n : ℝ)), mul_pos hK'pos (Real.rpow_pos_of_pos hC _), ?_⟩
  intro φ hφ
  set c : ℝ := C / φ ^ ((1 : ℝ) / 6) with hc
  have hφpos : 0 < φ := by linarith
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos hC (Real.rpow_pos_of_pos hφpos _)
  have hc1pos : 0 < c ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have hc1 : c ^ (1 / (n : ℝ)) = C ^ (1 / (n : ℝ)) * φ ^ (-(1 / (6 * (n : ℝ)))) := by
    have hφ1 : (0 : ℝ) < φ ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hφpos _
    rw [hc, Real.div_rpow (le_of_lt hC) (le_of_lt hφ1), div_eq_mul_inv]
    congr 1
    rw [← Real.rpow_neg (le_of_lt hφ1), ← Real.rpow_mul (le_of_lt hφpos)]
    congr 1
    field_simp
  -- the three thresholds
  set ξ₁ : ℝ := K' * c ^ (1 / (n : ℝ)) * v / (3 * Vu) with hξ₁
  set ξ₃ : ℝ := K' * v / (3 * (Kτ * (4 : ℝ) ^ (1 / (n : ℝ)))) with hξ₃
  have hξ₃one : 1 < ξ₃ := by
    have h1 : 0 < Kτ * (4 : ℝ) ^ (1 / (n : ℝ)) := by positivity
    rw [hξ₃, hK']
    field_simp
    nlinarith
  have hN1 : 1 ≤ NN d n := by
    rw [NN]
    exact Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hξ₁pos : 0 < ξ₁ := by
    rw [hξ₁]
    have hVu : 0 < Vu := by
      rw [hVu]
      exact ENNReal.toReal_pos hunitne0' hunitnetop'
    positivity
  -- eventual facts
  have hev1 : ∀ᶠ A : ℝ in atTop, (16 * Real.log (A * φ) + 1) ^ NN d n ≤ A ^ NN d n * ξ₁ :=
    log_eventually d n φ hφ ξ₁ hξ₁pos
  have hev2 : ∀ᶠ A : ℝ in atTop, Ku * A ^ (NN d n - 1) ≤ A ^ NN d n * (K' * c ^ (1 / (n : ℝ)) / 3) := by
    filter_upwards [eventually_ge_atTop (max 1 (3 * Ku / (K' * c ^ (1 / (n : ℝ)))))] with A hA
    have hA1 : 1 ≤ A := le_trans (le_max_left _ _) hA
    have hA0 : 0 ≤ A := by linarith
    have hKu : Ku ≤ A * (K' * c ^ (1 / (n : ℝ)) / 3) := by
      have h3 : 3 * Ku / (K' * c ^ (1 / (n : ℝ))) ≤ A := le_trans (le_max_right _ _) hA
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < K' * c ^ (1 / (n : ℝ)))] at h3
      linarith
    have hNpos : 0 < NN d n := by omega
    have hsplit : A ^ NN d n = A * A ^ (NN d n - 1) := by
      have h1 : NN d n = (NN d n - 1) + 1 := by omega
      conv_lhs => rw [h1]
      rw [pow_succ]
      ring
    rw [hsplit]
    have hnn : 0 ≤ A ^ (NN d n - 1) := by positivity
    nlinarith [hKu, hnn, hA0]
  have hev3 : ∀ᶠ A : ℝ in atTop, (A + 1) ^ NN d n ≤ A ^ NN d n * ξ₃ := by
    have hξ₃pos : 0 < ξ₃ := by linarith [hξ₃one]
    have hη : 0 < ξ₃ ^ (1 / (NN d n : ℝ)) := Real.rpow_pos_of_pos hξ₃pos _
    have hηN : (ξ₃ ^ (1 / (NN d n : ℝ))) ^ NN d n = ξ₃ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hξ₃pos)]
      norm_num
    have hη1 : 1 < ξ₃ ^ (1 / (NN d n : ℝ)) := Real.one_lt_rpow hξ₃one (by positivity)
    filter_upwards [eventually_ge_atTop (max 1 (1 / (ξ₃ ^ (1 / (NN d n : ℝ)) - 1)) + 1)] with A hA
    have hA1 : 1 ≤ A := by
      have h2 : (1 : ℝ) ≤ max 1 (1 / (ξ₃ ^ (1 / (NN d n : ℝ)) - 1)) := le_max_left _ _
      linarith
    have h3 : 1 / (ξ₃ ^ (1 / (NN d n : ℝ)) - 1) ≤ A := by
      have h2 : 1 / (ξ₃ ^ (1 / (NN d n : ℝ)) - 1)
          ≤ max 1 (1 / (ξ₃ ^ (1 / (NN d n : ℝ)) - 1)) := le_max_right _ _
      linarith
    have h2A : A + 1 ≤ A * ξ₃ ^ (1 / (NN d n : ℝ)) := by
      rw [div_le_iff₀ (by linarith : 0 < ξ₃ ^ (1 / (NN d n : ℝ)) - 1)] at h3
      nlinarith
    have hb := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ A + 1) h2A (NN d n)
    rw [mul_pow, hηN] at hb
    exact hb
  have hevlog : ∀ᶠ A : ℝ in atTop, 1 ≤ Real.log (A * φ) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1 / φ)] with A hA
    have hA0 : 0 < A := lt_of_lt_of_le (div_pos (Real.exp_pos 1) hφpos) hA
    have he : Real.exp 1 ≤ A * φ := by
      rw [div_le_iff₀ hφpos] at hA
      exact hA
    exact (Real.le_log_iff_exp_le (y := A * φ)
      (mul_pos (lt_of_lt_of_le (div_pos (Real.exp_pos 1) hφpos) hA) hφpos)).mpr he
  filter_upwards [hev1, hev2, hev3, hevlog, eventually_ge_atTop (1 : ℝ)] with A h1 h2 h3 hlog1 hA1
  -- the three counts
  have hc3 := count_good_le d n hd hn hKτ hτvol hpropp hscalep hIscalep hcones hpack hfin
    (Real.log (A * φ)) c A hlog1 hcpos hA1
  have hc2 : ((Uset d n A).ncard : ℝ) ≤ Ku * A ^ (NN d n - 1) := hbnd A hA1
  -- the set decomposition
  set S : Set (Mon d n → ℤ) := {a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ IPt d n (toR a) ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c} with hSdef
  set T1 : Set (Mon d n → ℤ) := {a : Mon d n → ℤ | eNorm a ≤ 16 * Real.log (A * φ)} with hT1def
  set W : Set (Mon d n → ℤ) := {a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ IPt d n (toR a) ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c ∧ 16 * Real.log (A * φ) ≤ eNorm a} with hWdef
  set Gn : Set (Mon d n → ℤ) := {a : Mon d n → ℤ | eNorm a ≤ A ∧ IPt d n (toR a) ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c ∧ 16 * Real.log (A * φ) ≤ eNorm a ∧
      (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y)} with hGndef
  set Gp : Set (Mon d n → ℤ) := {a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ IPt d n (toR a) ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c ∧ 16 * Real.log (A * φ) ≤ eNorm a ∧
      (∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y)} with hGpdef
  -- containment of the primitive sets
  have hSsub : primSet d n A (fun a => RealSol d n a ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c) ⊆ S := by
    rintro a ⟨hI, hnorm, hsol', hτ⟩
    rw [hSdef]
    exact ⟨hI, hnorm, hsol a hsol', hτ⟩
  have hprim : primCount d n A (fun a => RealSol d n a ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c) ≤ (S.ncard : ℝ) := by
    rw [primCount]
    exact_mod_cast Set.ncard_le_ncard hSsub ((hfin A).subset (fun a ha => by
      rw [hSdef] at ha; exact ha.2.1))
  have hSsplit : S ⊆ T1 ∪ W := by
    intro a ha
    rw [hSdef] at ha
    obtain ⟨hI, hAe, hIP, hτ⟩ := ha
    rw [hT1def, hWdef, Set.mem_union]
    by_cases h4 : 16 * Real.log (A * φ) ≤ eNorm a
    · exact Or.inr ⟨hI, hAe, hIP, hτ, h4⟩
    · exact Or.inl (le_of_lt (not_le.mp h4))
  have hWsplit : W ⊆ Uset d n A ∪ Gp := by
    intro a ha
    rw [hWdef] at ha
    obtain ⟨hI, hAe, hIP, hτ, h4⟩ := ha
    rw [hGpdef, Set.mem_union]
    by_cases h5 : ∀ y : Mon d n → ℝ, rNorm (toR a - y) ≤ 1 → IPt d n y
    · exact Or.inr ⟨hI, hAe, hIP, hτ, h4, h5⟩
    · exact Or.inl ⟨hI, hAe, hIP, h5⟩
  -- finiteness
  have hUfin : (Uset d n A).Finite := (hfin A).subset (fun a ha => ha.2.1)
  have hT1fin : T1.Finite := (hfin (16 * Real.log (A * φ))).subset (fun a ha => by
    rw [hT1def] at ha; exact ha)
  have hWfin : W.Finite := (hfin A).subset (fun a ha => by
    rw [hWdef] at ha; exact ha.2.1)
  have hGpfin : Gp.Finite := (hfin A).subset (fun a ha => by
    rw [hGpdef] at ha; exact ha.2.1)
  have hGnfin : Gn.Finite := (hfin A).subset (fun a ha => by
    rw [hGndef] at ha; exact ha.1)
  -- the three counts
  have hT1le : (T1.ncard : ℝ) * v ≤ (16 * Real.log (A * φ) + 1) ^ NN d n * Vu := by
    have hcs := count_small_le d n hn hpack hfin hballscale (16 * Real.log (A * φ)) (by positivity)
    rw [hT1def, hv, hVu]
    exact hcs
  have hc3' : (Gn.ncard : ℝ) * v ≤ (A + 1) ^ NN d n * (Kτ * (4 * c) ^ (1 / (n : ℝ))) := by
    rw [hGndef, hv]
    exact hc3
  have hGle : (Gp.ncard : ℝ) * v ≤ (A + 1) ^ NN d n * (Kτ * (4 * c) ^ (1 / (n : ℝ))) := by
    have hsub : Gp ⊆ Gn := by
      intro a ha
      rw [hGpdef] at ha
      obtain ⟨hI, hAe, hIP, hτ, h4, h5⟩ := ha
      rw [hGndef]
      exact ⟨hAe, hIP, hτ, h4, h5⟩
    have hle : (Gp.ncard : ℝ) ≤ (Gn.ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hGnfin
    calc (Gp.ncard : ℝ) * v ≤ (Gn.ncard : ℝ) * v :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hvpos)
      _ ≤ (A + 1) ^ NN d n * (Kτ * (4 * c) ^ (1 / (n : ℝ))) := hc3'
  -- the natural-number decompositions
  have hcard_nat : S.ncard ≤ T1.ncard + W.ncard :=
    le_trans (Set.ncard_le_ncard hSsplit (hT1fin.union hWfin)) (Set.ncard_union_le _ _)
  have hWcard_nat : W.ncard ≤ (Uset d n A).ncard + Gp.ncard :=
    le_trans (Set.ncard_le_ncard hWsplit (hUfin.union hGpfin)) (Set.ncard_union_le _ _)
  -- the target constant
  set Ab : ℝ := A ^ NN d n * (c ^ (1 / (n : ℝ))) * v * K' with hAbdef
  have hAbpos : 0 < Ab := by
    rw [hAbdef]
    have hApos : 0 < A := by linarith
    exact mul_pos (mul_pos (mul_pos (pow_pos hApos _) (Real.rpow_pos_of_pos hcpos _)) hvpos)
      hK'pos
  have hVu_ne : Vu ≠ 0 := ne_of_gt hVu_pos
  have hUle : ((Uset d n A).ncard : ℝ) * v ≤ Ab / 3 := by
    have h := mul_le_mul_of_nonneg_right (le_trans hc2 h2) (le_of_lt hvpos)
    calc ((Uset d n A).ncard : ℝ) * v
        ≤ (A ^ NN d n * (K' * c ^ (1 / (n : ℝ)) / 3)) * v := h
      _ = Ab / 3 := by rw [hAbdef]; ring
  have b1 : (T1.ncard : ℝ) * v ≤ Ab / 3 := by
    calc (T1.ncard : ℝ) * v
        ≤ (16 * Real.log (A * φ) + 1) ^ NN d n * Vu := hT1le
      _ ≤ (A ^ NN d n * ξ₁) * Vu := mul_le_mul_of_nonneg_right h1 ENNReal.toReal_nonneg
      _ = A ^ NN d n * (K' * c ^ (1 / (n : ℝ)) * v / 3) := by
            rw [hξ₁]
            field_simp
      _ = Ab / 3 := by rw [hAbdef]; ring
  have hKtpos : 0 < Kτ * (4 : ℝ) ^ (1 / (n : ℝ)) := by positivity
  have b3 : (Gp.ncard : ℝ) * v ≤ Ab / 3 := by
    calc (Gp.ncard : ℝ) * v
        ≤ (A + 1) ^ NN d n * (Kτ * (4 * c) ^ (1 / (n : ℝ))) := hGle
      _ ≤ (A ^ NN d n * ξ₃) * (Kτ * (4 * c) ^ (1 / (n : ℝ))) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = A ^ NN d n * ((K' * v / 3) * c ^ (1 / (n : ℝ))) := by
            rw [hξ₃, Real.mul_rpow (by norm_num) (le_of_lt hcpos)]
            field_simp [ne_of_gt hKtpos]
      _ = Ab / 3 := by rw [hAbdef]; ring
  -- assemble
  have hWb : (W.ncard : ℝ) * v ≤ 2 * (Ab / 3) := by
    have hWr : (W.ncard : ℝ) ≤ ((Uset d n A).ncard : ℝ) + (Gp.ncard : ℝ) := by
      exact_mod_cast hWcard_nat
    have hmul : (W.ncard : ℝ) * v ≤ (((Uset d n A).ncard : ℝ) + (Gp.ncard : ℝ)) * v :=
      mul_le_mul_of_nonneg_right hWr (le_of_lt hvpos)
    nlinarith [hmul, hUle, b3]
  have hsum : (T1.ncard : ℝ) * v + (W.ncard : ℝ) * v ≤ Ab := by
    linarith [b1, hWb, hAbpos]
  have hfin1 : primCount d n A (fun a => RealSol d n a ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c) * v ≤ Ab := by
    have hSv : (S.ncard : ℝ) * v ≤ Ab := by
      have hcard_real : (S.ncard : ℝ) ≤ (T1.ncard : ℝ) + (W.ncard : ℝ) := by
        exact_mod_cast hcard_nat
      calc (S.ncard : ℝ) * v ≤ ((T1.ncard : ℝ) + (W.ncard : ℝ)) * v :=
            mul_le_mul_of_nonneg_right hcard_real (le_of_lt hvpos)
        _ = (T1.ncard : ℝ) * v + (W.ncard : ℝ) * v := by ring
        _ ≤ Ab := hsum
    have hp := mul_le_mul_of_nonneg_right hprim (le_of_lt hvpos)
    linarith [hp, hSv]
  have hfin2 : primCount d n A (fun a => RealSol d n a ∧
      tauArch d n (toR a) (Real.log (A * φ)) < c)
      ≤ A ^ NN d n * (c ^ (1 / (n : ℝ))) * K' := by
    have h := hfin1
    rw [hAbdef] at h
    refine le_of_mul_le_mul_right ?_ hvpos
    nlinarith [h]
  rw [hc1] at hfin2
  calc primCount d n A (fun a => RealSol d n a ∧
        tauArch d n (toR a) (Real.log (A * φ)) < c)
      ≤ A ^ NN d n * (C ^ (1 / (n : ℝ)) * φ ^ (-(1 / (6 * (n : ℝ))))) * K' := hfin2
    _ = K' * C ^ (1 / (n : ℝ)) * A ^ NN d n / φ ^ (1 / (6 * (n : ℝ))) := by
        rw [Real.rpow_neg (le_of_lt hφpos), div_eq_mul_inv]
        ring
end Work.HP
