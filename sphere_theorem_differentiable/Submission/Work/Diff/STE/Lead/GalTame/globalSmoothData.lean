import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.exists_partition_compact
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.B3.integral_pd_comp_le_compact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- **The smooth global data attached to an open cover of a compact set, a family of local
diffeomorphisms and a family of coefficients smooth on the cover.**

This is the abstract (B3-independent) content of the construction
`Work.Diff.STE.B3.exists_smooth_data` of `Submission/Work/Diff/STE/B3/mat_ENormSq_le_clean.lean`
(whose private proof should be transcribed, with `V i` for `goodSetZeta D i j`, `f i` for
`tMapFun D i j` and `S i c d` for `recoCoeff D i j ab.1 ab.2 c d`; the hypotheses `hfi`, `hfd` there
come from `injOn_tMapFun_goodSet`, `tMapFun_det_ne_zero`).

Given a compact set `Kc`, an open cover `(V i)` of it, functions `f i` which are smooth, injective
and have non-vanishing Jacobian determinant on `V i`, and coefficients `S i c d` smooth on `V i`,
there are: a smooth partition of unity `ψ` on `Kc` subordinate to `(V i)` with compact supports, a
globally smooth transition `Tt i` equal to `f i` on the support of `ψ i` (and on an open
`U i ⊇ tsupport (ψ i)`, `U i ⊆ V i`, on which `Tt i` is injective with invertible Jacobian), and
smooth compactly supported coefficients `G i c d` equal to `ψ i · S i c d` where `ψ i ≠ 0` and `0`
where `ψ i = 0`, together with a single constant `Ctr` bounding the transfer estimate
`∫_{ℝⁿ} ‖∂^{γ}(G_{icd} · (u ∘ Tt i))‖² ≤ Ctr Σ_{k ≤ |γ|} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`
for all smooth `1`-periodic `u` and all `|γ| ≤ m`, with **the whole-space integral on the left**. -/
theorem globalSmoothData {n : ℕ} {ι : Type*} [Fintype ι]
    (Kc : Set (Fin n → ℝ)) (hKc : IsCompact Kc)
    (V : ι → Set (Fin n → ℝ)) (hVo : ∀ i, IsOpen (V i)) (hVc : Kc ⊆ ⋃ i, V i)
    (f : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (hf : ∀ i, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (f i) (V i))
    (hfi : ∀ i, Set.InjOn (f i) (V i))
    (hfd : ∀ (i : ι) (z : Fin n → ℝ), z ∈ V i → (fderiv ℝ (f i) z).det ≠ 0)
    (S : ι → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hS : ∀ (i : ι) (c d : Fin n), ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (S i c d) (V i))
    (m : ℕ) :
    ∃ (ψ : ι → (Fin n → ℝ) → ℝ) (Tt : ι → (Fin n → ℝ) → (Fin n → ℝ))
      (U : ι → Set (Fin n → ℝ))
      (G : ι → Fin n → Fin n → (Fin n → ℝ) → ℝ) (Ctr : ℝ),
      (∀ i, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ V i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ z ∈ Kc, ∑ i, ψ i z = 1) ∧
      (∀ i, IsOpen (U i)) ∧
      (∀ i, U i ⊆ V i) ∧
      (∀ i, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Tt i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, Set.InjOn (Tt i) (U i)) ∧
      (∀ (i : ι) (z : Fin n → ℝ), z ∈ U i → (fderiv ℝ (Tt i) z).det ≠ 0) ∧
      (∀ (i : ι) (z : Fin n → ℝ), z ∈ U i → Tt i z = f i z) ∧
      (∀ (i : ι) (z : Fin n → ℝ), ψ i z ≠ 0 → Tt i z = f i z) ∧
      (∀ (i : ι) (c d : Fin n), ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (G i c d)) ∧
      (∀ (i : ι) (c d : Fin n), HasCompactSupport (G i c d)) ∧
      (∀ (i : ι) (c d : Fin n), tsupport (G i c d) ⊆ V i) ∧
      (∀ (i : ι) (c d : Fin n) (z : Fin n → ℝ), ψ i z ≠ 0 → G i c d z = ψ i z * S i c d z) ∧
      (∀ (i : ι) (c d : Fin n) (z : Fin n → ℝ), ψ i z = 0 → G i c d z = 0) ∧
      0 ≤ Ctr ∧
      (∀ (i : ι) (c d : Fin n) (j' : ℕ) (γ : Fin j' → Fin n), j' ≤ m →
        ∀ (u : (Fin n → ℝ) → ℂ), ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u →
        Work.Diff.STE.Periodic1 u →
        ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j' γ
            (fun z => ((G i c d z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ Ctr * ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin n,
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) := by
  classical
  -- ## the smooth partition of unity subordinate to the cover `(V i)`
  obtain ⟨ψ, hψsm, -, hψsupp, hψcpt, hψsum⟩ :=
    Work.Diff.STE.B3.exists_partition_compact Kc hKc V hVo hVc
  -- ## the smoothed transitions, with the open sets on which they are genuine diffeomorphisms
  have hTt : ∀ i : ι, ∃ (Tt : (Fin n → ℝ) → (Fin n → ℝ)) (U : Set (Fin n → ℝ)),
      IsOpen U ∧ U ⊆ V i ∧ tsupport (ψ i) ⊆ U ∧
      ContDiff ℝ (⊤ : ℕ∞) Tt ∧ Set.InjOn Tt U ∧
      (∀ z ∈ U, (fderiv ℝ Tt z).det ≠ 0) ∧ (∀ z ∈ U, Tt z = f i z) := by
    intro i
    obtain ⟨δ, hδpos, hδsub⟩ := (hψcpt i).exists_cthickening_subset_open (hVo i) (hψsupp i)
    have hKcpt : IsCompact (Metric.cthickening (δ / 2) (tsupport (ψ i))) := (hψcpt i).cthickening
    have hKsub : Metric.cthickening (δ / 2) (tsupport (ψ i)) ⊆ V i :=
      (Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) _).trans hδsub
    obtain ⟨ρ, hρsm, hρone, -, hρprod⟩ :=
      Work.Diff.STE.D.bump_smul_smooth (Metric.cthickening (δ / 2) (tsupport (ψ i))) (V i)
        hKcpt (hVo i) hKsub (f i) (hf i)
    have hTform : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z • f i z) := by
      simpa only [smul_eq_mul] using hρprod
    have hUsub : Metric.thickening (δ / 2) (tsupport (ψ i)) ⊆ V i :=
      (Metric.thickening_subset_cthickening _ _).trans hKsub
    have heqOn : ∀ z ∈ Metric.thickening (δ / 2) (tsupport (ψ i)),
        (fun w => ρ w • f i w) z = f i z := by
      intro z hz
      show ρ z • f i z = f i z
      rw [hρone z ((Metric.thickening_subset_cthickening _ _) hz), one_smul]
    refine ⟨fun z => ρ z • f i z, Metric.thickening (δ / 2) (tsupport (ψ i)),
      Metric.isOpen_thickening, hUsub, ?_, hTform, ?_, ?_, heqOn⟩
    · exact Metric.self_subset_thickening (by linarith : (0:ℝ) < δ / 2) _
    · intro a ha b hb hab
      have h1 : f i a = f i b := by rw [← heqOn a ha, ← heqOn b hb, hab]
      exact hfi i (hUsub ha) (hUsub hb) h1
    · intro z hz
      have hev : (fun w => ρ w • f i w) =ᶠ[nhds z] f i :=
        Filter.eventually_of_mem ((Metric.isOpen_thickening).mem_nhds hz) fun w hw => heqOn w hw
      rw [hev.fderiv_eq]
      exact hfd i z (hUsub hz)
  choose Tt U hUopen hUsubV hUsub hTtsm hTinj hTdet hTteq using hTt
  have hTtone : ∀ i z, ψ i z ≠ 0 → Tt i z = f i z :=
    fun i z hz => hTteq i z (hUsub i (subset_closure (Function.mem_support.mpr hz)))
  -- ## the smoothed coefficients, with the aggregated transfer constants
  have hG : ∀ (i : ι) (c d : Fin n),
      ∃ (Gicd : (Fin n → ℝ) → ℝ) (Cicd : ℝ),
      0 ≤ Cicd ∧ ContDiff ℝ (⊤ : ℕ∞) Gicd ∧ HasCompactSupport Gicd ∧
      tsupport Gicd ⊆ V i ∧
      (∀ z, ψ i z ≠ 0 → Gicd z = ψ i z * S i c d z) ∧
      (∀ z, ψ i z = 0 → Gicd z = 0) ∧
      (∀ (j' : ℕ) (γ : Fin j' → Fin n), j' ≤ m →
        ∀ (u : (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j' γ
            (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ Cicd * ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin n,
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) := by
    intro i c d
    obtain ⟨ρ, hρsm, hρone, -, hρprod⟩ :=
      Work.Diff.STE.D.bump_smul_smooth (tsupport (ψ i)) (V i)
        (hψcpt i) (hVo i) (hψsupp i) (S i c d) (hS i c d)
    set Gicd : (Fin n → ℝ) → ℝ := fun z => ψ i z * (ρ z * S i c d z) with hGicd
    have hGsm : ContDiff ℝ (⊤ : ℕ∞) Gicd := by
      rw [hGicd]
      simpa only [smul_eq_mul] using (hψsm i).mul hρprod
    have hGsup : tsupport Gicd ⊆ tsupport (ψ i) := by
      rw [hGicd]
      exact tsupport_mul_subset_left
    have hGcpt : HasCompactSupport Gicd :=
      (hψcpt i).of_isClosed_subset (isClosed_tsupport Gicd) hGsup
    have hGgood : tsupport Gicd ⊆ V i := hGsup.trans (hψsupp i)
    have htsuppC : tsupport (fun z => ((Gicd z : ℝ) : ℂ)) = tsupport Gicd := by
      rw [tsupport, tsupport]
      congr 1
      ext z
      exact not_congr Complex.ofReal_eq_zero
    -- the transfer constants, aggregated over all `(j',γ)` with `j' ≤ m`
    have htr : ∀ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n)),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (Fin n → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec (t.1 : ℕ) t.2
            (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ C * ∑ k ∈ Finset.range ((t.1 : ℕ) + 1), ∑ l' : Fin k → Fin n,
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 := by
      intro t
      have hfK : IsCompact (tsupport (fun z => ((Gicd z : ℝ) : ℂ))) := by
        rw [htsuppC]; exact hGcpt
      obtain ⟨C, hCnn, hCb⟩ := Work.Diff.STE.B3.integral_pd_comp_le_compact
        (T := Tt i) (hT := hTtsm i)
        (f := fun z => ((Gicd z : ℝ) : ℂ))
        (hf := Complex.ofRealCLM.contDiff.comp hGsm) (hK := hfK) (U := U i)
        (hU := hUopen i)
        (hUf := by rw [htsuppC]; exact fun z hz => hUsub i (hGsup hz))
        (hinj := hTinj i) (hdet := hTdet i) (t.1 : ℕ) t.2
      exact ⟨C, hCnn, hCb⟩
    choose Cind hCindnn hCindb using htr
    refine ⟨Gicd, ∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n)),
      (Cind t + 1), ?_, hGsm, hGcpt, hGgood, ?_, ?_, ?_⟩
    · exact Finset.sum_nonneg fun t _ => by linarith [hCindnn t]
    · intro z hz
      show ψ i z * (ρ z * S i c d z) = ψ i z * S i c d z
      rw [hρone z (subset_closure (Function.mem_support.mpr hz)), one_mul]
    · intro z hz
      show ψ i z * (ρ z * S i c d z) = 0
      rw [hz, zero_mul]
    · intro j' γ hj' u hu hup
      have h1 : Cind ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩
          ≤ ∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n)), (Cind t + 1) := by
        have h2 := Finset.single_le_sum
          (f := fun t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n)) => (Cind t + 1))
          (fun t _ => by linarith [hCindnn t])
          (Finset.mem_univ ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩)
        linarith
      calc ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec j' γ
              (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          = ∫ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec
              ((⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ :
                (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n))).1 : ℕ)
              (⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ :
                (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n))).2
              (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2 := rfl
        _ ≤ Cind ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ *
              ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin n,
                ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
            hCindb ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ u hu hup
        _ ≤ (∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin n)), (Cind t + 1)) *
              ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin n,
                ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg
              fun l' _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)
  choose G Cicd hCicdnn hGsm hGcpt hGgood hGone hGzero hGb using hG
  refine ⟨ψ, Tt, U, G,
    ∑ i : ι, ∑ c : Fin n, ∑ d : Fin n, (Cicd i c d + 1),
    hψsm, hψsupp, hψcpt, hψsum, hUopen, hUsubV, hTtsm, hUsub, hTinj, hTdet, hTteq, hTtone,
    hGsm, hGcpt, hGgood, hGone, hGzero, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun d _ => by linarith [hCicdnn i c d]
  · intro i c d j' γ hj' u hu hup
    have h1 : Cicd i c d ≤ ∑ i : ι, ∑ c : Fin n, ∑ d : Fin n, (Cicd i c d + 1) := by
      have h2 := Finset.single_le_sum
        (f := fun i : ι => ∑ c : Fin n, ∑ d : Fin n, (Cicd i c d + 1))
        (fun i _ => Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ =>
          by linarith [hCicdnn i c d]) (Finset.mem_univ i)
      have h3 := Finset.single_le_sum
        (f := fun c : Fin n => ∑ d : Fin n, (Cicd i c d + 1))
        (fun c _ => Finset.sum_nonneg fun d _ => by linarith [hCicdnn i c d]) (Finset.mem_univ c)
      have h4 := Finset.single_le_sum
        (f := fun d : Fin n => (Cicd i c d + 1))
        (fun d _ => by linarith [hCicdnn i c d]) (Finset.mem_univ d)
      linarith
    exact le_trans (hGb i c d j' γ hj' u hu hup)
      (mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg
        fun l' _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _))

end Work.Diff.STE.Lead.GalTame
