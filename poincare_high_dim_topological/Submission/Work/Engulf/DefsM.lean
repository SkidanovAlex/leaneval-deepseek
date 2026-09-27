import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools

/-! Universe facade (lead, NOTES_LEAD_poincare_E4c.md §B): state new lemmas with {M : Type*}, BM M, ToolsAllM M; never name a universe. -/

open Set Metric PL

universe u


/-! (B) universe-name-free facade for request statements -/
namespace Work.Engulf
def BM (M : Type u) [MetricSpace M] (n p k : ℕ) : Prop := B.{u} n p k

/-- `C1 n p k` at the universe of `M`. -/
def C1M (M : Type u) [MetricSpace M] (n p k : ℕ) : Prop := C1.{u} n p k

/-- `L7 n p q` at the universe of `M`. -/
def L7M (M : Type u) [MetricSpace M] (n p q : ℕ) : Prop := L7.{u} n p q

/-- `L7c n p q` at the universe of `M`. -/
def L7cM (M : Type u) [MetricSpace M] (n p q : ℕ) : Prop := L7c.{u} n p q

def ToolsAllM (M : Type u) [MetricSpace M] (n : ℕ) : Type := ToolsAll.{u} n

-- a request statement written with `Type*` and no `universe` line elaborates and is usable:
example {n p q : ℕ} {M : Type*} [MetricSpace M] (T : ToolsAllM M n) (hB : BM M n p q)
    {V X : Set M} {N : ℕ} {Γ : Cx N} {H L : Set (E N)} {f : E N → M}
    (A : Amb n p M V) (c : Cfg n p V X Γ H L f) (hXV : X ⊆ V) (hb : BadCard Γ H f V q) :
    Engulfs V X Γ H L f 1 :=
  hB M V X N Γ H L f A c hXV hb 1 one_pos
end Work.Engulf
