import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.deTurck_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the DeTurck components along a continuous family of sections

The localised component `D.R i (deTurckSec hLC g₀ h …) a b z` of the DeTurck section is, by
`Work.Diff.STE.D.deTurckSec_apply`, the product of the `σ`-independent weight
`D.psi i z * √(D.dens i z)` with the value `deTurckOp (smetOf h …) g₀ x u v` of the DeTurck operator
at the chart point `x = D.pt i z` and the two frame vectors `u = D.e i a x`, `v = D.e i b x`.

The second conjunct of `Work.Diff.STE.Lead.deTurck_bound` is exactly the statement that those
operator values are *sequentially* continuous along a family of sections that is bounded in
`BNorm k` (for one `k` with `finrank ℝ E + 12 < 2k`), uniformly elliptic between `lam g₀` and
`K g₀`, and convergent in `BNorm k`.  The hypothesis `hcont` of the target supplies this
`BNorm k`-convergence along the filter `𝓝[Ico 0 τ₀] t`; the sequential characterisation of
`Tendsto` for the countably generated filter `𝓝[Ico 0 τ₀] t` (`Filter.tendsto_of_seq_tendsto`)
turns it into the required `ContinuousWithinAt`.

Technically, `hcont` only controls `σ` *in* `Ico 0 τ₀` and `deTurck_bound` needs the bounds for
*every* index of the sequence, so the sequence is capped at `0` outside `Ico 0 τ₀` (which is
harmless: it is eventually equal to the given sequence, and `0 ∈ Ico 0 τ₀` whenever the interval
is nonempty).
-/

namespace Work.Diff.STE.Lead

theorem continuous_deTurckSec_R
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (τ₀ : ℝ) (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k) (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hsym : ∀ (t : ℝ) (x : M) (u v : TangentSpace I x), (U t) x u v = (U t) x v u)
    (hpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (U t) x v v)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hell : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (U t) x v v)
    (hub : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      (U t) x v v ≤ K * g₀.inner x v v)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ContinuousWithinAt
      (fun σ : ℝ => D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ)
        (hsym σ) (hpos σ) (hsm σ)) a b z)
      (Set.Ico (0 : ℝ) τ₀) t := by
  classical
  intro t ht
  -- a degree large enough for the DeTurck bound
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Module.finrank ℝ E + 12 < 2 * k :=
    ⟨Module.finrank ℝ E + 13, by omega⟩
  -- the DeTurck operator values are sequentially continuous along `BNorm k`-convergent families
  have hbd := (deTurck_bound (I := I) (M := M) D hLC k hk lam K hlam).2
  -- the localised component is the (constant) weight times the DeTurck operator value
  have hident : ∀ s : ℝ,
      D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U s) (hsym s) (hpos s) (hsm s)) a b z
        = (D.psi i z * Real.sqrt (D.dens i z))
          * Work.Diff.STE.DeTurck.deTurckOp
              (Work.Diff.STE.D.smetOf (I := I) (U s) (hsym s) (hpos s) (hsm s)) g₀
              (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z)) := by
    intro s
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat,
      Work.Diff.STE.D.deTurckSec_apply]
  -- sequential characterisation of the convergence along `𝓝[Ico 0 τ₀] t`
  refine Filter.tendsto_of_seq_tendsto ?_
  intro σ hσ
  obtain ⟨hσt, hσS⟩ := tendsto_nhdsWithin_iff.1 hσ
  -- `0` is in the interval (it is nonempty since `t` is)
  have h0S : (0 : ℝ) ∈ Set.Ico (0 : ℝ) τ₀ := by
    obtain ⟨h0, hlt⟩ := ht
    exact Set.left_mem_Ico.mpr (lt_of_le_of_lt h0 hlt)
  -- cap the sequence at `0`, so that it lies in the interval at *every* index
  let τ : ℕ → ℝ := fun n => if σ n ∈ Set.Ico (0 : ℝ) τ₀ then σ n else 0
  have hτS : ∀ n, τ n ∈ Set.Ico (0 : ℝ) τ₀ := by
    intro n
    by_cases hn : σ n ∈ Set.Ico (0 : ℝ) τ₀
    · simpa only [τ, ite_eq_left hn] using hn
    · simpa only [τ, ite_eq_right hn] using h0S
  have hτeq : τ =ᶠ[Filter.atTop] σ := by
    filter_upwards [hσS] with n hn
    simp only [τ, ite_eq_left hn]
  have hτt : Filter.Tendsto τ Filter.atTop (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσt.congr' hτeq.symm, Filter.Eventually.of_forall hτS⟩
  -- convergence of the DeTurck operator values along the capped sequence
  have hstep : Filter.Tendsto
      (fun n : ℕ => Work.Diff.STE.DeTurck.deTurckOp
        (Work.Diff.STE.D.smetOf (I := I) (U (τ n)) (hsym (τ n)) (hpos (τ n)) (hsm (τ n)))
        g₀ (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z)))
      Filter.atTop
      (nhds (Work.Diff.STE.DeTurck.deTurckOp
        (Work.Diff.STE.D.smetOf (I := I) (U t) (hsym t) (hpos t) (hsm t))
        g₀ (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z)))) :=
    hbd (B k) (fun n => U (τ n)) (U t)
      (fun n => hsym (τ n)) (fun n => hpos (τ n)) (fun n => hsm (τ n))
      (hsym t) (hpos t) (hsm t)
      (fun n => hUB (τ n) (hτS n) k) (hUB t ht k)
      (fun n x v => hell (τ n) (hτS n) x v) (fun x v => hell t ht x v)
      (fun n x v => hub (τ n) (hτS n) x v) (fun x v => hub t ht x v)
      ((hcont t ht k).comp hτt)
      (D.pt i z) (D.e i a (D.pt i z)) (D.e i b (D.pt i z))
  -- transfer to the localised component, and undo the capping
  have hFτ : Filter.Tendsto
      (fun n : ℕ => D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U (τ n))
        (hsym (τ n)) (hpos (τ n)) (hsm (τ n))) a b z)
      Filter.atTop
      (nhds (D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t)
        (hsym t) (hpos t) (hsm t)) a b z)) := by
    have h1 := hstep.const_mul (D.psi i z * Real.sqrt (D.dens i z))
    rw [← hident t] at h1
    exact h1.congr' (Filter.Eventually.of_forall fun n => (hident (τ n)).symm)
  exact hFτ.congr' (hτeq.mono fun n hn => congrArg
    (fun s : ℝ => D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U s)
      (hsym s) (hpos s) (hsm s)) a b z) hn)

end Work.Diff.STE.Lead
