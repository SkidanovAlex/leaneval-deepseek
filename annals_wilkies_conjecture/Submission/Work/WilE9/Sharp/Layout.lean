/-
  WilE9 / Sharp — the coordinate layouts of the two systems of the BNZ §3 transport.

  ## The pulled-back system (`pb`)

  Ambient `ℝ^{Npb n m}`, split as base `x : ℝⁿ` (the *original* coordinates of `f`) and fibre
  `(s, y, w, τ, u, aux)`, where

  * `s` is the new unknown (it will solve `s = f x`),
  * `y i = ψ (x i)`, `w i = psig (x i)`, tied to `x` by `y i = x i * w i`, `y i ^ 2 + w i ^ 2 = 1`,
  * `τ = ψ s`, `u = psig s`, tied by `τ = s * u`, `τ ^ 2 + u ^ 2 = 1`,
  * `aux` are the stratum's auxiliary coordinates.

  The equations are `2n + m + 3` in number and the fibre has `2n + m + 3` coordinates, so the
  system is square; `WilE9.Ift.ift_exists`/`ift_identity` then compute the derivatives of `s` in
  the *`x`*-directions as `P_L / Q^{2|L|}` for `P_L = iftP pbChain pbF 0 L`, `Q = jQ pbChain pbF`.
  This is how the `ψ`-coordinate change is turned into the BNZ formula *without* any Faà di Bruno
  expansion.

  ## The extended system (`ex`)

  Ambient `ℝ^{Next n m}`, base `y : ℝⁿ` (the `ψ`-coordinates, i.e. the coordinates of a `*`-piece)
  and output `σ` at position `n`, then the fibre `(w, u, τ, aux, υ)`.  The equations are the
  stratum's own description (`y i ^ 2 + w i ^ 2 = 1`, `τ ^ 2 + u ^ 2 = 1`, the equations `h` and
  the basic condition of the stratum), the two algebraic relations `σ ^ 2 + υ ^ 2 = 1` and the
  cleared form of `σ * Q^(2|L|) = υ * P_L`.  Projecting the first `n+1` coordinates gives the
  `ψ`-image of the graph of `∂^L f`, whence `Gen.star` closes the argument.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.EffInput

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## Dimensions -/

/-- Number of equations (= number of fibre coordinates) of the pulled-back system. -/
def qpb (n m : ℕ) : ℕ := 2 * n + m + 3

/-- Ambient dimension of the pulled-back system. -/
def Npb (n m : ℕ) : ℕ := n + qpb n m

/-- Ambient dimension of the extended system.  Written as `(n+1) + (n+m+3)` so that the base
plus output (the first `n+1` coordinates) and the fibre (the last `n+m+3`) split definitionally,
which is what `projFirst (n+1) (n+m+3)` needs. -/
def Next (n m : ℕ) : ℕ := (n + 1) + (n + m + 3)

theorem Next_eq (n m : ℕ) : Next n m = 2 * n + m + 4 := by simp [Next]; ring

theorem Npb_eq (n m : ℕ) : Npb n m = 3 * n + m + 3 := by simp [Npb, qpb]; ring

/-- The two ways of writing the ambient dimension of a `*`-piece: base `n+1` with fibre `m` (the
shape forced by `StarPiece`/`projFirst`), or base `n` with fibre `1 + m` (the shape forced by
`jm`/`eaD`/`Fin.natAdd`). -/
theorem addSplit (n m : ℕ) : (n + 1) + m = n + (1 + m) := by omega

/-! ## Coordinates of the pulled-back system -/

/-- The base coordinate `xᵢ` of the pulled-back system. -/
def pbX (n m : ℕ) (i : Fin n) : Fin (Npb n m) := ⟨i.val, by have := i.isLt; simp [Npb, qpb]; omega⟩

/-- The coordinate `s` of the pulled-back system. -/
def pbS (n m : ℕ) : Fin (Npb n m) := ⟨n, by simp [Npb, qpb]⟩

/-- The coordinate `y i = ψ (x i)`. -/
def pbY (n m : ℕ) (i : Fin n) : Fin (Npb n m) :=
  ⟨n + 1 + i.val, by have := i.isLt; simp [Npb, qpb]; omega⟩

/-- The coordinate `w i = psig (x i)`. -/
def pbW (n m : ℕ) (i : Fin n) : Fin (Npb n m) :=
  ⟨2 * n + 1 + i.val, by have := i.isLt; simp [Npb, qpb]; omega⟩

/-- The coordinate `τ = ψ s`. -/
def pbT (n m : ℕ) : Fin (Npb n m) := ⟨3 * n + 1, by simp [Npb, qpb]; omega⟩

/-- The coordinate `u = psig s`. -/
def pbU (n m : ℕ) : Fin (Npb n m) := ⟨3 * n + 2, by simp [Npb, qpb]; omega⟩

/-- The auxiliary coordinate `aux a`. -/
def pbA (n m : ℕ) (a : Fin m) : Fin (Npb n m) :=
  ⟨3 * n + 3 + a.val, by have := a.isLt; simp [Npb, qpb]; omega⟩

/-! ## The fibre indices of the pulled-back system (the last `qpb n m` coordinates) -/

/-- The fibre index of `s`. -/
def fS (n m : ℕ) : Fin (qpb n m) := ⟨0, by simp [qpb]⟩

/-- The fibre index of `y i`. -/
def fY (n m : ℕ) (i : Fin n) : Fin (qpb n m) :=
  ⟨1 + i.val, by have := i.isLt; simp [qpb]; omega⟩

/-- The fibre index of `w i`. -/
def fW (n m : ℕ) (i : Fin n) : Fin (qpb n m) :=
  ⟨n + 1 + i.val, by have := i.isLt; simp [qpb]; omega⟩

/-- The fibre index of `τ`. -/
def fT (n m : ℕ) : Fin (qpb n m) := ⟨2 * n + 1, by simp [qpb] <;> omega⟩

/-- The fibre index of `u`. -/
def fU (n m : ℕ) : Fin (qpb n m) := ⟨2 * n + 2, by simp [qpb] <;> omega⟩

/-- The fibre index of `aux a`. -/
def fA (n m : ℕ) (a : Fin m) : Fin (qpb n m) :=
  ⟨2 * n + 3 + a.val, by have := a.isLt; simp [qpb]; omega⟩

/-! ## Coordinates of the extended system -/

/-- The base coordinate `y i`. -/
def exY (n m : ℕ) (i : Fin n) : Fin (Next n m) :=
  ⟨i.val, by have := i.isLt; simp [Next]; omega⟩

/-- The output coordinate `σ`. -/
def exSig (n m : ℕ) : Fin (Next n m) := ⟨n, by simp [Next]; omega⟩

/-- The coordinate `w i`. -/
def exW (n m : ℕ) (i : Fin n) : Fin (Next n m) :=
  ⟨n + 1 + i.val, by have := i.isLt; simp [Next]; omega⟩

/-- The coordinate `u`. -/
def exU (n m : ℕ) : Fin (Next n m) := ⟨2 * n + 1, by simp [Next]; omega⟩

/-- The coordinate `τ`. -/
def exT (n m : ℕ) : Fin (Next n m) := ⟨2 * n + 2, by simp [Next]; omega⟩

/-- The auxiliary coordinate `aux a`. -/
def exA (n m : ℕ) (a : Fin m) : Fin (Next n m) :=
  ⟨2 * n + 3 + a.val, by have := a.isLt; simp [Next]; omega⟩

/-- The coordinate `υ = psig σ`. -/
def exV (n m : ℕ) : Fin (Next n m) := ⟨2 * n + 3 + m, by simp [Next]; omega⟩

/-! ## The stratum's coordinates inside the two systems -/

/-- The stratum's ambient coordinates `Fin (n + (1 + m))` (`y`, then `τ`, then `aux`) mapped into
the pulled-back ambient: `y` at `pbY`, `τ` at `pbT`, `aux` at `pbA`. -/
def sIdxPb (n m : ℕ) : Fin (n + (1 + m)) → Fin (Npb n m) := fun i =>
  if h : (i : ℕ) < n then pbY n m ⟨i, h⟩
  else if h2 : (i : ℕ) = n then pbT n m
  else pbA n m ⟨(i : ℕ) - (n + 1), by have := i.isLt; omega⟩

/-- The stratum's ambient coordinates mapped into the extended ambient. -/
def sIdxE (n m : ℕ) : Fin (n + (1 + m)) → Fin (Next n m) := fun i =>
  if h : (i : ℕ) < n then exY n m ⟨i, h⟩
  else if h2 : (i : ℕ) = n then exT n m
  else exA n m ⟨(i : ℕ) - (n + 1), by have := i.isLt; omega⟩

end Work.WilE9.Sharp
