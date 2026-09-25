import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.Trace.Basic

namespace Commons.FieldTheory.Galois

/-- In a finite Galois extension `L/K` there is an element `b` of trace one whose
Galois conjugates `σ • b` form a `K`-basis of `L` (a *normal basis of trace one*).

Starting from a normal basis generator `b₀` supplied by `IsGalois.normalBasis`, the trace
`Tr(b₀)` cannot vanish: otherwise, by `Algebra.trace_eq_of_algEquiv`, the trace would vanish
on the whole basis `{σ • b₀}`, contradicting `Algebra.trace_ne_zero` for the separable
extension `L/K`. Hence `b = Tr(b₀)⁻¹ • b₀` has trace `1`, and scaling a normal basis by a
nonzero constant leaves it a basis. -/
theorem exists_normalBasis_trace_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ b : L, Algebra.trace K L b = 1 ∧
      LinearIndependent K (fun σ : Gal(L/K) => σ • b) ∧
      Submodule.span K (Set.range fun σ : Gal(L/K) => σ • b) = ⊤ := by
  classical
  -- A normal basis generator `b₀ = e 1`, where `e σ = σ • b₀` is a `K`-basis of `L`.
  let e : Module.Basis Gal(L/K) K L := IsGalois.normalBasis K L
  let b₀ : L := e 1
  have hb₀e : ∀ σ : Gal(L/K), e σ = σ • b₀ := by
    intro σ
    rw [IsGalois.normalBasis_apply]
    rfl
  -- The trace of `b₀` is nonzero.
  have htne : Algebra.trace K L b₀ ≠ 0 := by
    intro h0
    have hvan : ∀ σ : Gal(L/K), Algebra.trace K L (e σ) = 0 := by
      intro σ
      rw [hb₀e σ, AlgEquiv.smul_def, Algebra.trace_eq_of_algEquiv σ b₀, h0]
    have htrzero : Algebra.trace K L = 0 := by
      apply LinearMap.ext_on e.span_eq
      rintro x ⟨σ, rfl⟩
      exact hvan σ
    exact Algebra.trace_ne_zero K L htrzero
  -- Rescale to make the trace equal to one.
  let c : K := (Algebra.trace K L b₀)⁻¹
  have hc : c ≠ 0 := inv_ne_zero htne
  let u : Kˣ := Units.mk0 c hc
  let B : Module.Basis Gal(L/K) K L := e.unitsSMul (fun _ => u)
  have hB : ∀ σ : Gal(L/K), B σ = c • e σ := by
    intro σ
    rw [Module.Basis.unitsSMul_apply]
    simp [u]
  have hfun : (fun σ : Gal(L/K) => σ • (c • b₀)) = B := by
    funext σ
    rw [hB σ, hb₀e σ]
    simp [AlgEquiv.smul_def, map_smul]
  refine ⟨c • b₀, ?_, ?_, ?_⟩
  · rw [map_smul]
    simp only [smul_eq_mul]
    rw [inv_mul_cancel₀ htne]
  · rw [hfun]
    exact B.linearIndependent
  · rw [hfun]
    exact B.span_eq

end Commons.FieldTheory.Galois