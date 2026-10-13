import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.SlicedSurrogateDefs

namespace Work.WilkG4c

/-- The value `4 * surrogateSlice - 2` inverts the affine normalisation `D ↦ (D + 2)/4` of the
sliced surrogate: on the smooth locus the surrogate is `(D + 2)/4` with
`D = ∂_M (slice (f l) x) (γ l x)`, so `4 * surrogateSlice - 2 = D`, and off the locus the value
is the constant `1/2`, for which `4 * (1/2) - 2 = 0`.  Hence the bound `|D| ≤ 1` transports
directly to `|4 * surrogateSlice - 2| ≤ 1`. -/
theorem CdpSurrogateAbs {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (hb : |iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f l) x) (γ l x)
        (fun j => Pi.single (M.get j) 1)| ≤ 1) :
    |4 * Work.WilkG4c.surrogateSlice p n f γ M l x - 2| ≤ 1 := by
  by_cases h : ContDiffAt ℝ M.length (Work.WilkG4c.slice (f l) x) (γ l x)
  · -- On the smooth locus the surrogate is `(D + 2)/4`, so `4 * surrogateSlice - 2 = D`.
    rw [surrogateSlice_of_mem h]
    have key : 4 * ((iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f l) x) (γ l x)
          (fun j => Pi.single (M.get j) 1) + 2) / 4) - 2
        = iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f l) x) (γ l x)
            (fun j => Pi.single (M.get j) 1) := by
      ring
    rw [key]
    exact hb
  · -- Off the smooth locus the surrogate is the constant `1/2`.
    rw [surrogateSlice_of_not_mem h]
    norm_num

end Work.WilkG4c

namespace Work.WilG4c

/-- Path-derived alias of `Work.WilkG4c.CdpSurrogateAbs`, for tooling and callers that read the
declaration name off the module path (`Submission/Work/WilG4c/CdpSurrogateAbs`). -/
theorem CdpSurrogateAbs {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {M : List (Fin n)} {l : Fin p → ℝ} {x : ℝ}
    (hb : |iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f l) x) (γ l x)
        (fun j => Pi.single (M.get j) 1)| ≤ 1) :
    |4 * Work.WilkG4c.surrogateSlice p n f γ M l x - 2| ≤ 1 :=
  _root_.Work.WilkG4c.CdpSurrogateAbs hb

end Work.WilG4c
