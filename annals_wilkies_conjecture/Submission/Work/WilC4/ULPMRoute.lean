/-
  WilC4/ULPMRoute : vocabulary for the proof of H1 (`Work.WilC4.Route.realULPM`,
  `Route.ModelULPM ℝ`) of the C4 route (`sources/wilkiesC4route/wilkies_C4_route.md`).

  Fix a `∅`-definable family `Y ⊆ ℝ^{k+2}` which *is* a family of graphs: for every parameter
  tuple `c : Fin k → ℝ` and every `x` there is at most one `y` with `Fin.cons x (Fin.cons y c) ∈ Y`.
  The fibre is the partial function `f_c : x ↦ y`.

  This module fixes the elementary vocabulary about `f_c` used by the ULPM proof, and proves the
  bookkeeping lemmas (the junk value is a genuine value on the domain, uniqueness of the value,
  the ratio is well defined wherever both values are).  Everything is stated for the *relation*
  `Y`, because the value function `valY` produced by `Classical.choose` is not itself definable
  and only the relation can enter a `Definable` statement.

  Design of the proof of `ModelULPM ℝ` (see `NOTES.md` in this directory for the long version):

  * `B` — a `∅`-definable breakpoint family `B ⊆ ℝ^{k+1}` (the `B` of `Route.ModelULPM`) whose
    fibres are uniformly finite, outside whose fibres the fibre function is *nice*: the domain is
    a union of intervals, `f_c` is continuous and either identically zero or nowhere zero on the
    complement of `B_c`, and the ratio `r_c x = f_c (2 x) / f_c x` is monotone there
    (`ulpm_mono_param`).
  * `Qs` — a *finite* set of rational exponents: the end-exponents at `0` and `+∞` (from `hPB`
    and its inversion) together with the exponent `0`.
  * the comparison `f_c x₂ / f_c x₁ ≍ (x₂ / x₁) ^ q` on each *slot* of `B_c`, where a slot is
    the set of `x > 0` lying on the same side (factor `N`) of every breakpoint of `B_c`.

  The two structural facts about slots that the final assembly uses:

  * `SameSide` puts every pair `x₁, x₂` used in the conclusion into the same slot
    (`inSlot_of_sameSide`, `side_iff_of_sameSide`), and both points are at multiplicative
    distance `> N` from every positive breakpoint (`depth_gt_of_sameSide`).
  * the slots between the positive breakpoints `b₁ < … < b_m` are the intervals `(0, b₁/N)`,
    `(N b_i, b_{i+1}/N)`, `(N b_m, ∞)` (`slot_shape`).
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.Defs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4.Route

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## 1. The fibre function of a family of graphs -/

/-- The graph relation of the family `Y ⊆ ℝ^{k+2}`: `y` is a value of the fibre at `(c, x)`. -/
def Gr (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ) : Prop :=
  Fin.cons x (Fin.cons y c) ∈ Y

/-- The domain of the fibre at the parameter `c`. -/
def InD (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) : Prop := ∃ y : ℝ, Gr Y c x y

/-- The value of the fibre at `(c, x)`; the junk value `0` outside the domain. -/
def valY (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) : ℝ :=
  if h : InD Y c x then Classical.choose h else 0

theorem valY_mem (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) (h : InD Y c x) :
    Gr Y c x (valY Y c x) := by
  unfold valY
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The value of the fibre is unique, so any value equals `valY`. -/
theorem eq_valY {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {c : Fin k → ℝ} {x y : ℝ} (h : Gr Y c x y) : y = valY Y c x :=
  hfun c x y (valY Y c x) h (valY_mem Y c x ⟨y, h⟩)

/-- `x` is in the domain iff `valY` is a genuine value there. -/
theorem inD_iff_gr_valY (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) :
    InD Y c x ↔ Gr Y c x (valY Y c x) :=
  ⟨fun h => valY_mem Y c x h, fun h => ⟨valY Y c x, h⟩⟩

/-- The ratio `r_c x = f_c (2 x) / f_c x` which drives the whole argument: the growth exponent
of `f_c` at the scale `x` is `log₂` of this number. -/
def ratioY (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x : ℝ) : ℝ :=
  valY Y c (2 * x) / valY Y c x

/-- The graph of the ratio, as a family of graphs in `x` with parameters `c`. -/
def RatGraph (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | ∃ y y' : ℝ, Gr Y (fun j : Fin k => v j.succ.succ) (v 0) y ∧ y ≠ 0 ∧
      Gr Y (fun j : Fin k => v j.succ.succ) (2 * v 0) y' ∧ v 1 * y = y'}

/-- The graph of the ratio is a family of graphs (this is what makes `hPB` and
`ulpm_mono_param` applicable to it). -/
theorem ratGraph_is_graph {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y') :
    ∀ (c : Fin k → ℝ) (x w w' : ℝ), Fin.cons x (Fin.cons w c) ∈ RatGraph Y →
      Fin.cons x (Fin.cons w' c) ∈ RatGraph Y → w = w' := by
  intro c x w w' hw hw'
  simp only [RatGraph, Set.mem_ofPred_eq] at hw hw'
  obtain ⟨y, y', hy, hy0, hy', hwy⟩ := hw
  obtain ⟨z, z', hz, hz0, hz', hwz⟩ := hw'
  simp only [Fin.cons_zero, Fin.cons_succ] at hy hy' hz hz'
  have hwyy : w * y = y' := by simpa using hwy
  have hwzz : w' * z = z' := by simpa using hwz
  have hyz : y = z := hfun c x y z hy hz
  subst hyz
  have hyz' : y' = z' := hfun c (2 * x) y' z' hy' hz'
  subst hyz'
  exact mul_right_cancel₀ hy0 (by rw [hwyy, hwzz])

/-! ## 2. Slots: the components cut out by the breakpoints of `B` -/

/-- `x` lies in a slot of the breakpoint family `B` at parameter `c`: `x` is on the "outer" side
(factor `N`) of every breakpoint. -/
def InSlot (B : Set (Fin (k + 1) → ℝ)) (N : ℕ) (c : Fin k → ℝ) (x : ℝ) : Prop :=
  ∀ b : ℝ, Fin.cons b c ∈ B → (N : ℝ) * b < x ∨ x < b / (N : ℝ)

/-- `SameSide` puts both points into slots. -/
theorem inSlot_of_sameSide {B : Set (Fin (k + 1) → ℝ)} {N : ℕ} (hN : 0 < N) {c : Fin k → ℝ}
    {x₁ x₂ : ℝ} (h : SameSide N {x : ℝ | Fin.cons x c ∈ B} x₁ x₂) :
    InSlot B N c x₁ ∧ InSlot B N c x₂ := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor <;> intro b hb
  · rcases h b hb with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr (by rw [lt_div_iff₀ hN']; linarith)
  · rcases h b hb with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inl h2
    · exact Or.inr (by rw [lt_div_iff₀ hN']; linarith)

/-- `SameSide` puts both points strictly on the same side of every *positive* breakpoint. -/
theorem side_iff_of_sameSide {B : Set (Fin (k + 1) → ℝ)} {N : ℕ} (hN : 0 < N) {c : Fin k → ℝ}
    {x₁ x₂ : ℝ} (h : SameSide N {x : ℝ | Fin.cons x c ∈ B} x₁ x₂) :
    ∀ b : ℝ, 0 < b → Fin.cons b c ∈ B → (((N : ℝ) * b < x₁) ↔ ((N : ℝ) * b < x₂)) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  intro b hb0 hb
  rcases h b hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hb1 : ¬ ((N : ℝ) * b < x₁) := by
      intro hc
      have hlt : x₁ < b / (N : ℝ) := by rw [lt_div_iff₀ hN']; linarith
      have hlt' : x₁ * (N : ℝ) < b := by rw [lt_div_iff₀ hN'] at hlt; exact hlt
      have hmul : (N : ℝ) * ((N : ℝ) * b) < (N : ℝ) * x₁ := mul_lt_mul_of_pos_left hc hN'
      have hbb : (N : ℝ) * ((N : ℝ) * b) < b := by nlinarith [hmul, hlt']
      have hsq : (1 : ℝ) ≤ (N : ℝ) * (N : ℝ) := by nlinarith [hN1]
      have hb_le : b ≤ (N : ℝ) * (N : ℝ) * b := by
        have := mul_le_mul_of_nonneg_right hsq (le_of_lt hb0)
        nlinarith [this]
      nlinarith [hbb, hb_le]
    have hb2 : ¬ ((N : ℝ) * b < x₂) := by
      intro hc
      have hlt : x₂ < b / (N : ℝ) := by rw [lt_div_iff₀ hN']; linarith
      have hlt' : x₂ * (N : ℝ) < b := by rw [lt_div_iff₀ hN'] at hlt; exact hlt
      have hmul : (N : ℝ) * ((N : ℝ) * b) < (N : ℝ) * x₂ := mul_lt_mul_of_pos_left hc hN'
      have hbb : (N : ℝ) * ((N : ℝ) * b) < b := by nlinarith [hmul, hlt']
      have hsq : (1 : ℝ) ≤ (N : ℝ) * (N : ℝ) := by nlinarith [hN1]
      have hb_le : b ≤ (N : ℝ) * (N : ℝ) * b := by
        have := mul_le_mul_of_nonneg_right hsq (le_of_lt hb0)
        nlinarith [this]
      nlinarith [hbb, hb_le]
    exact ⟨fun hc => absurd hc hb1, fun hc => absurd hc hb2⟩

/-- Both points of a `SameSide` pair (with positive breakpoint `b`) are at multiplicative
distance `> N` from `b`: the "depth" that makes the final telescoping work. -/
theorem depth_gt_of_sameSide {B : Set (Fin (k + 1) → ℝ)} {N : ℕ} (hN : 0 < N) {c : Fin k → ℝ}
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (h : SameSide N {x : ℝ | Fin.cons x c ∈ B} x₁ x₂) :
    ∀ b : ℝ, 0 < b → Fin.cons b c ∈ B →
      ((N : ℝ) * b < x₁ ∧ (N : ℝ) * b < x₂) ∨ ((N : ℝ) * x₁ < b ∧ (N : ℝ) * x₂ < b) := by
  intro b hb0 hb
  rcases h b hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-! ## 4. Deep points and the cluster exponent set `E` -/

/-- `x` is `B`-deep for the breakpoint family `B₀` at parameter `c`: the multiplicative interval
`[x/(2B), 2Bx]` misses every breakpoint of `B₀_c`.  This is the set of points at which the fibre
function `f_c` is "far from its singularities at scale `B`", with room for the doubling
`t ↦ 2t` that the telescoping uses. -/
def IsDeep (B₀ : Set (Fin (k + 1) → ℝ)) (c : Fin k → ℝ) (B : ℕ) (x : ℝ) : Prop :=
  ∀ b : ℝ, Fin.cons b c ∈ B₀ →
    ¬ (x / (2 * (B : ℝ)) ≤ b ∧ b ≤ 2 * (B : ℝ) * x)

/-- **The cluster exponent set** of the family `Y` relative to the breakpoint family `B₀`: `ρ` is
in `E` if for every `B` there is a `B`-deep point `x` with the ratio `f_c(2t)/f_c(t)` within
`1/B` of `ρ` for every `t ∈ [x/B, xB]` at which it is defined and `f_c t ≠ 0`.

The intended claim is that `E` is **finite** and that `E ⊆ {2^q : q ∈ ℚ}`; see
`Submission/Work/WilC4/ULPM_NOTES.md` §3–§4bis.  The exponent of a slot of the final breakpoint
family is `log₂` of an element of `E`, so `Qs := {q : 2^q ∈ E} ∪ {0}` is the finite exponent set
of `Route.ModelULPM`. -/
def ClusterE (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set ℝ :=
  {ρ | ∀ B : ℕ, 0 < B → ∃ (c : Fin k → ℝ) (x : ℝ),
    0 < x ∧ IsDeep B₀ c B x ∧
      ∀ t : ℝ, x / (B : ℝ) ≤ t → t ≤ x * (B : ℝ) →
        ∀ y y' : ℝ, Gr Y c t y → Gr Y c (2 * t) y' → y ≠ 0 →
          |y' / y - ρ| ≤ 1 / (B : ℝ)}

/-- `E` is a set of one-tuples, in the shape of `RExpExist`. -/
def ClusterEfam (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) : Set (Fin 1 → ℝ) :=
  {v | v 0 ∈ ClusterE Y B₀}

theorem mem_clusterEfam {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {v : Fin 1 → ℝ} : v ∈ ClusterEfam Y B₀ ↔ v 0 ∈ ClusterE Y B₀ := Iff.rfl

end Work.WilC4.Route
