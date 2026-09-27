import Mathlib
import Submission.Work.EQ.DefsCore

set_option linter.dupNamespace false

namespace Work.EQ

namespace Work.EQ

open Filter _root_.Topology

/-- The solutions of `ζ ^ k = c` with `0 < k` are finite: they are the roots of the nonzero
polynomial `X ^ k - C c`. -/
private lemma finite_setOf_pow_eq {k : ℕ} (hk : 0 < k) (c : ℂ) : {ζ : ℂ | ζ ^ k = c}.Finite := by
  refine ((Polynomial.X ^ k - Polynomial.C c).roots.toFinset.finite_toSet).subset ?_
  intro ζ hζ
  simp only [Set.mem_ofPred_eq] at hζ ⊢
  rw [Finset.mem_coe, Multiset.mem_toFinset,
    Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hk c),
    Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, hζ, sub_self]

/-- The solutions of `κ * ζ ^ k = c` with `κ ≠ 0` and `0 < k` are finite (divide by `κ`). -/
private lemma finite_setOf_mul_pow_eq {κ c : ℂ} {k : ℕ} (hκ : κ ≠ 0) (hk : 0 < k) :
    ({ζ : ℂ | κ * ζ ^ k = c}).Finite := by
  refine (finite_setOf_pow_eq hk (c / κ)).subset ?_
  intro ζ hζ
  simp only [Set.mem_ofPred_eq] at hζ ⊢
  rw [eq_div_iff hκ, mul_comm]
  exact hζ

/-- **The `ψ₁`-fibre over a point is finite when the component is compact modulo punctures.**
If `S ⊆ H0` is closed in `H0`, if `ψ₁` is injective on a neighbourhood of each point of `H0`
(intersected with `H0`), and if the part of `S` over the point `u₁` is covered by a compact subset
of `H0` together with the half-images of finitely many punctured charts, then the fibre of `S`
over `u₁` is finite. -/
theorem fibre_finite_of_cover {a : ℝ} {h : ℂ → ℂ} {S : Set ChainData} {u₁ : ℂ}
    (hSH : S ⊆ H0 a h)
    (hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S)
    (hinj : ∀ q ∈ H0 a h, ∃ U : Set ChainData, IsOpen U ∧ q ∈ U ∧
      ∀ q₁ ∈ U, q₁ ∈ H0 a h → ∀ q₂ ∈ U, q₂ ∈ H0 a h → q₁.2.1 = q₂.2.1 → q₁ = q₂)
    {C : Set ChainData} (hC : IsCompact C) (hCH : C ⊆ H0 a h)
    {m : ℕ} {e : Fin m → ℂ → ChainData} {u₀ : Fin m → ℂ} {k : Fin m → ℕ}
    (hchart : ∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i))
    (hcov : S ∩ {q | q.2.1 = u₁} ⊆
      C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})) :
    (S ∩ {q | q.2.1 = u₁}).Finite := by
  classical
  -- `T` is the `ψ₁`-fibre of `S` over `u₁`.
  set T : Set ChainData := S ∩ {q | q.2.1 = u₁} with hTdef
  have hTS : T ⊆ S := fun q hq => by rw [hTdef] at hq; exact hq.1
  have hT1 : ∀ q ∈ T, q.2.1 = u₁ := fun q hq => by rw [hTdef] at hq; exact hq.2
  have hTH : T ⊆ H0 a h := fun q hq => hSH (hTS hq)
  -- Local injectivity of `ψ₁` on `H0` makes `T` discrete.
  have hdis : IsDiscrete T := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro q hq
    obtain ⟨U, hUo, hqU, hinjU⟩ := hinj q (hTH hq)
    refine ⟨U, hUo, ?_⟩
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [Set.mem_singleton_iff]
      exact hinjU x hx.1 (hTH hx.2) q hqU (hTH hq) (by rw [hT1 x hx.2, hT1 q hq])
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hqU, hq⟩
  -- `T ∩ C` is closed in `C`: a limit point of `T ∩ C` lies in `C ⊆ H0`, in `closure S`, and in
  -- the closed set `{ψ₁ = u₁}`, hence in `S`, hence in `T`.
  have hclosTC : IsClosed (T ∩ C) := by
    rw [← closure_subset_iff_isClosed]
    intro q hq
    have hqC : q ∈ C := hC.isClosed.closure_subset (closure_mono Set.inter_subset_right hq)
    have hq1 : q.2.1 = u₁ := by
      have hcl : IsClosed {x : ChainData | x.2.1 = u₁} :=
        isClosed_eq (by fun_prop) continuous_const
      have hmem : q ∈ closure {x : ChainData | x.2.1 = u₁} :=
        closure_mono (fun x hx => hT1 x hx.1) hq
      rwa [hcl.closure_eq] at hmem
    have hqS : q ∈ S := hScl q (closure_mono (fun x hx => hTS hx.1) hq) (hCH hqC)
    rw [hTdef]
    exact ⟨⟨hqS, hq1⟩, hqC⟩
  -- Compactness plus discreteness gives finiteness of the compact part.
  have hTCfin : (T ∩ C).Finite :=
    (hC.of_isClosed_subset hclosTC Set.inter_subset_right).finite (hdis.mono Set.inter_subset_left)
  -- On a punctured chart, `ψ₁ (e i ζ) = u₀ i + κ ζ ^ k i`; the fibre condition `ψ₁ = u₁` is then
  -- the polynomial equation `κ ζ ^ k i = u₁ - u₀ i`, which has finitely many solutions.
  have hchartfin : ∀ i : Fin m, (T ∩ e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})).Finite := by
    intro i
    obtain ⟨hk, -, κ, hκ, hmem, -, -, -, -⟩ := hchart i
    have hZfin : ({ζ : ℂ | κ * ζ ^ (k i) = u₁ - u₀ i}).Finite :=
      finite_setOf_mul_pow_eq hκ hk
    refine (hZfin.image (e i)).subset ?_
    rintro q ⟨hqT, ζ, hζball, heq⟩
    rw [← heq] at hqT ⊢
    have hζ1 : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
      refine ⟨?_, hζball.2⟩
      have hb : ζ ∈ Metric.ball (0 : ℂ) (1 / 2) := hζball.1
      rw [Metric.mem_ball, dist_zero_right] at hb ⊢
      linarith
    have hψ : (e i ζ).2.1 = u₀ i + κ * ζ ^ k i := (hmem ζ hζ1).2
    refine ⟨ζ, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [eq_sub_iff_add_eq, add_comm]
    rw [← hψ]
    exact hT1 (e i ζ) hqT
  have h2 : (T ∩ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})).Finite := by
    rw [Set.inter_iUnion]
    exact Set.finite_iUnion hchartfin
  -- Assemble: `T ⊆ (T ∩ C) ∪ (T ∩ ⋃ᵢ eᵢ '' punctured ball)`.
  refine (hTCfin.union h2).subset ?_
  intro q hq
  rcases hcov hq with hq' | hq'
  · exact Or.inl ⟨hq, hq'⟩
  · exact Or.inr ⟨hq, hq'⟩

end Work.EQ

/- The file template opens `namespace Work.EQ` once for the module and the requested statement
opened it once more, so the declaration whose proof is above lives at the name
`Work.EQ.Work.EQ.fibre_finite_of_cover`; the `end` above pops back to `Work.EQ`.  The same lemma
is therefore also exposed under the requested name `Work.EQ.fibre_finite_of_cover`. -/

open Filter _root_.Topology

/-- **The `ψ₁`-fibre over a point is finite when the component is compact modulo punctures.**
Alias of `Work.EQ.Work.EQ.fibre_finite_of_cover` under the requested name. -/
theorem fibre_finite_of_cover {a : ℝ} {h : ℂ → ℂ} {S : Set ChainData} {u₁ : ℂ}
    (hSH : S ⊆ H0 a h)
    (hScl : ∀ q ∈ closure S, q ∈ H0 a h → q ∈ S)
    (hinj : ∀ q ∈ H0 a h, ∃ U : Set ChainData, IsOpen U ∧ q ∈ U ∧
      ∀ q₁ ∈ U, q₁ ∈ H0 a h → ∀ q₂ ∈ U, q₂ ∈ H0 a h → q₁.2.1 = q₂.2.1 → q₁ = q₂)
    {C : Set ChainData} (hC : IsCompact C) (hCH : C ⊆ H0 a h)
    {m : ℕ} {e : Fin m → ℂ → ChainData} {u₀ : Fin m → ℂ} {k : Fin m → ℕ}
    (hchart : ∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i))
    (hcov : S ∩ {q | q.2.1 = u₁} ⊆
      C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})) :
    (S ∩ {q | q.2.1 = u₁}).Finite :=
  Work.EQ.Work.EQ.fibre_finite_of_cover hSH hScl hinj hC hCH hchart hcov

end Work.EQ
