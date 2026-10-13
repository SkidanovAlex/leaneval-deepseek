import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.RHSDataFepsNoTraces
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.EpsEngine.HkIntegrand_perz_six_noTraces
import Submission.Work.FTS.EpsEngine.HkMemIterAll
import Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8
import Submission.Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val
import Submission.Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val_six
import Submission.Work.FTS.EpsEngine.Feps_data_of_xball8
import Submission.Work.FTS.EpsEngine.Feps_gates_of_xball_curve

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/RHSDataFepsSix/exists_RHSData_feps_six.lean`

**The order-`6` per-curve data of the scheme's right-hand side.**

`Work.FTS.EpsEngine.RHSData α 6 T B (Feps α ρ ε Φs E) g₀ n` is the order-`6` instance of the
per-curve right-hand-side data of the interval-integral `ℋ`-lemma
(`EpsEngine/HkMemIterAll.lean`), needed by the order-`6` branch of the local step.  Its seven
fields are produced exactly as in the order-`4` case
(`Work.FTS.EpsEngine.exists_RHSData_feps_noTraces`), with the two genuinely new outputs:

* the **slot-sup gate at order `6`** — `Work.FTS.EpsEngine.EpsRHSP_slotSup_of_val_six`, the
  order-`6` lift of `EpsRHSP_slotSup_of_val` (all derivatives are routed onto the mollifier
  kernel, so only a *value* bound of `epsWP` is consumed, and the rank-one `L₁₂` correction stays
  at order `4`);
* the **per-`z` energy bound at order `6`** — `Work.FTS.EpsEngine.HkIntegrand_perz_six_noTraces`,
  which consumes the `ℋ⁸`-honesty of `Feps u`; the uniform `ℋ⁸`-size of `Feps` on the `XBall`
  class is `Work.FTS.EpsEngine.Feps_data_of_xball8` (whose membership half is
  `TenOfEight.HkMem_Jeps_gain_pos` at `k = 4`, `m = 4`).

The order-`6` (resp. order-`8`) `meas`/`joint` gates are the *parametric* siblings
`hmeas_slot_epsRHSP_fam_of_gate` (arbitrary slots) and
`hjoint_HkIntegrand_epsRHSP_fam_of_gate (k := 6)`.

Everything here is `sorry`-free.
-/

namespace Work.FTS.EpsEngine.RHSDataFepsSix

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)

set_option autoImplicit false

/-! ## The per-`z` energy bound of `Feps` along an `XBall` curve, at level `6` -/

/-- **The per-`z` energy bound of the scheme's right-hand side along an `XBall` curve, at level
`6`.**  This is the order-`6` analogue of `perz_Feps_noTraces`: the level-`6` `ℋ`-integrand of
`Feps u` is controlled per `z` by the uniform `ℋ⁸`-size of `Feps` on the `XBall` class. -/
theorem perz_Feps_six {α C₀ Ce Cs R ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F₀ : ℝ → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hX : ∀ s ∈ Set.Icc (0 : ℝ) T, XBall α ρ ε R C₀ (F₀ s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (Feps α ρ ε Φs E (F₀ s)) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by
  obtain ⟨Ce8, hCe8pos, hFeps8⟩ := Feps_data_of_xball8 hρ hα hε hε1 hR hEll hstar hml
  obtain ⟨Cc, hCcpos, hCc⟩ := HkIntegrand_perz_six_noTraces
  refine ⟨Cc * (1 + Ce8) ^ 2, by positivity, ?_⟩
  intro z hz s hs
  obtain ⟨hsm, hmem, hbd⟩ := hFeps8 (F₀ s) (hX s hs)
  have h := hCc α hα hsm hmem z hz
  have hnn : 0 ≤ Work.Spaces.HkNorm α 8 (Feps α ρ ε Φs E (F₀ s)) :=
    Work.Spaces.HkNorm_nonneg α 8 _
  have h1 : (1 + Work.Spaces.HkNorm α 8 (Feps α ρ ε Φs E (F₀ s))) ^ 2 ≤ (1 + Ce8) ^ 2 := by
    nlinarith [hCe8pos.le]
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (Feps α ρ ε Φs E (F₀ s)) z θ)
      ≤ Cc * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α 8 (Feps α ρ ε Φs E (F₀ s))) ^ 2 := h
    _ ≤ Cc * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce8) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hCcpos.le (by positivity))
    _ = Cc * (1 + Ce8) ^ 2 * (1 + (Work.Spaces.w z) ^ 2) := by ring

/-! ## The three gates of `Feps` along an `XBall` curve, at level `6` -/

/-- **The order-`6` gates of the projected `ε`-scheme's right-hand side along an `XBall` curve**:
the sliced a.e. strong measurability of every jet up to order `6`, the joint a.e. strong
measurability of the level-`6` `ℋ`-integrand, and the uniform slot bound on each compact
`K ⊆ Q0` — the order-`6` analogue of `Feps_gates_of_xball_curve`. -/
theorem Feps_gates_six {α C₀ R Ce Cs Lw δ ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc (0 : ℝ) δ, XBall α ρ ε R C₀ (slice g s))
    (hEq : ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ t ∈ Set.Icc (0 : ℝ) δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => slice g s z θ - slice g t z θ)
        ≤ Lw * (s - t) ^ 2) :
    (∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 6
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1) p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)).prod
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    ∧ (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 6 →
          |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j i hji z θ hQ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    exact hmeas_slot_epsRHSP_fam_of_gate hα hρ hε hε1 hEll hstar hml hR hLw
      hP hEq j i hz ⟨hθ0, hθ1⟩
  · exact hjoint_HkIntegrand_epsRHSP_fam_of_gate (k := 6)
      hα hρ hε hε1 hEll hstar hml hR hLw hP hEq
  · intro K hK hKQ
    rcases lt_or_ge δ 0 with hδneg | hδnonneg
    · have hemp : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt hδneg
      refine ⟨0, le_rfl, ?_⟩
      intro s hs
      rw [hemp] at hs
      exact absurd hs (by simp)
    · obtain ⟨CJ, _hCJpos, hXn6⟩ := Xn6_JfamP_le_of_XBall (ρ := ρ) hρ
      set B6 : ℝ := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) with hB6def
      set Ce' : ℝ := max Ce B6 with hCe'def
      have hb6 : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.StrongGlobal.Xn6 α
          (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce' :=
        fun s hs => le_trans (hXn6 hα hε hε1 (hP s hs)) (le_max_right _ _)
      have hEll' : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce' u (E u) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce' u (E u) :=
        fun u hu =>
          ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1
              (by rw [hCe'def]; exact le_max_left _ _),
           Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2
              (by rw [hCe'def]; exact le_max_left _ _)⟩
      have hC : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.ClassC.ClassC α
          (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
        fun s hs => (hP s hs).classC
      have hb4 : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.Nonlin.Xn α
          (slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2 :=
        fun s hs => (hP s hs).ball
      have hreg : ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) :=
        Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ)
          (Φs := Φs) (E := E) (g := g) (ε := ε) hα hEll hstar hC
      obtain ⟨KW, hKW, hn⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
        (α := α) (C₀ := C₀) (Ce := Ce') (Cs := Cs) (T := δ) (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun _ => g) (ε := fun _ => ε) hα hEll' hstar hml
        (fun _ s hs => hC s hs) (fun _ s hs => hb4 s hs) (fun _ s hs => hb6 s hs)
      have hnorm : ∃ KW' : ℝ, 0 ≤ KW' ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
            Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW' :=
        ⟨KW, hKW.le, fun s hs => hn 0 s hs⟩
      obtain ⟨C, hC0, hCb⟩ := EpsRHSP_slotSup_of_val_six (α := α) (C₀ := C₀)
        (Ce := Ce') (Cs := Cs) (T := δ) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
        hα hρ hε hε1 hδnonneg hEll' hstar hml hC hb4 hb6 hreg hnorm hK hKQ
      exact ⟨C, hC0, fun s hs q hq j i hji => hCb j i hji s hs q hq⟩

/-! ## The target -/

theorem exists_RHSData_feps_six {α C₀ Ce Cs R Lw ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (hT : 0 ≤ T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.EpsEngine.XBall α ρ ε R C₀
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s)) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.StrongEps.EpsSq α (fun z θ =>
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s z θ
            - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) t z θ)
          ≤ Lw * (s - t) ^ 2) →
      Work.FTS.EpsEngine.RHSData α 6 T B (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n := by
  obtain ⟨Ce', hCe'pos, hFeps6⟩ := Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (R := R) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  refine ⟨Ce', hCe'pos, ?_⟩
  intro n hP hEq
  set F₀ : ℝ → Fn := fun s => slice (iter (Feps α ρ ε Φs E) g₀ n) s with hF₀
  set G : Fam := fun z θ s => F₀ s z θ with hG
  have hslice : ∀ s : ℝ, slice G s = F₀ s := fun s => rfl
  have hRH : ∀ s : ℝ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E G s
      = Feps α ρ ε Φs E (F₀ s) := fun s => by
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice, hslice s]
  have hgates := Feps_gates_six (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := T) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) (g := G)
    hα hρ hε hε1 hEll hstar hml hR hLw
    (fun s hs => by rw [hslice s]; exact hP s hs)
    (fun s hs t ht => by rw [hslice s, hslice t]; exact hEq s hs t ht)
  obtain ⟨Cz, hCzpos, hCz⟩ := perz_Feps_six (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (R := R) (ε := ε) (T := T) (ρ := ρ) (Φs := Φs) (E := E) (F₀ := F₀)
    hρ hα hε hε1 hR hT hEll hstar hml (fun s hs => hP s hs)
  refine ⟨fun s hs => (hFeps6 (F₀ s) (hP s hs)).1,
    fun s hs => (hFeps6 (F₀ s) (hP s hs)).2.1,
    fun s hs => (hFeps6 (F₀ s) (hP s hs)).2.2,
    fun j i hji z θ hQ => by simpa only [hRH] using hgates.1 j i hji z θ hQ,
    by simpa only [hRH] using hgates.2.1,
    fun K hK hKQ => by
      obtain ⟨C, hC0, hCb⟩ := hgates.2.2 K hK hKQ
      exact ⟨C, hC0, fun s hs q hq j i hji => by simpa only [hRH] using hCb s hs q hq j i hji⟩,
    fun z hz => ⟨Cz * (1 + (Work.Spaces.w z) ^ 2), fun s hs => by simpa only [hRH] using hCz z hz s hs⟩⟩

end Work.FTS.EpsEngine.RHSDataFepsSix
