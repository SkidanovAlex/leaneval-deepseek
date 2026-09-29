import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ResMath.resE_defs

/-!
# Objects of the one-dimensional `B̃` word (paper Prop. 4.7(ii), Lemmas 4.8–4.12)

Fixes the map `Φ = B̃` and the static table `egTab` read by the word `q` of
`Submission/Work/Resample/sliceB1.lean`.  Everything is exact integer (fixed point) arithmetic.

`B̃ = P̃_s⁻¹ ∘ D̃' ∘ J̃' ∘ C̃ ∘ P̃_t`, with
`J̃' u = Σ_{j<n} (-1)^j (Ẽ^j (u/2))`, `n = ⌈ps/(α²(t-s))⌉`, `Ẽ` the truncated Gaussian
convolution of Lemma 4.11 with half-width `m = ⌊√p/(2α)⌋+1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Parameters -/

/-- Window half-width `m = ⌊√p/(2α)⌋ + 1 ≥ √p/(2α)`. -/
def egM (p α : ℕ) : ℕ := Nat.sqrt p / (2 * α) + 1

/-- Number of Neumann rounds `n = ⌈ps/(α²(t-s))⌉`. -/
def egN (p α s t : ℕ) : ℕ := (p * s - 1) / (α ^ 2 * (t - s)) + 1

/-- The kept shifts `h`, `0 < |h| ≤ m`. -/
def egHset (m : ℕ) : Finset ℤ := (Finset.Icc (-(m : ℤ)) (m : ℤ)).erase 0

/-- The kept shifts in ascending order: `[-m, …, -1] ++ [1, …, m]`. -/
def egHs (m : ℕ) : List ℤ :=
  ((List.range m).map (fun i : ℕ => (i : ℤ) - (m : ℤ))) ++
    ((List.range m).map (fun i : ℕ => (i : ℤ) + 1))

/-! ## The Gaussian weights -/

/-- True real weight of the shift `h` in row `ℓ` of `E`: `e^{-πα²((th/s+β_ℓ)²-β_{ℓ+h}²)}`. -/
noncomputable def egW (s t α : ℕ) (ℓ h : ℤ) : ℝ :=
  Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
    (((t : ℝ) * (h : ℝ) / (s : ℝ) + Work.ResMath.betaI s t ℓ) ^ 2 -
      (Work.ResMath.betaI s t (ℓ + h)) ^ 2)))

/-- The rounded integer weight `[2^p · egW]`. -/
noncomputable def egWi (p s t α : ℕ) (ℓ h : ℤ) : ℤ := HvdH.rnd ((2 : ℝ) ^ p * egW s t α ℓ h)

/-- The rounded diagonal weight of `D'`. -/
noncomputable def egWd (p s t α : ℕ) (ℓ : Fin s) : ℤ :=
  HvdH.rnd ((2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re)

/-! ## Index maps -/

/-- `σ_t k = (-s k) mod t`: the index map of `P̃_t`. -/
def egSigT (s t : ℕ) (k : ℕ) : ℕ := (t - s * k % t) % t

/-- `[tℓ/s]`: the index map of `C̃`. -/
def egRho (s t : ℕ) (ℓ : ℕ) : ℕ := (2 * t * ℓ + s) / (2 * s)

/-- The fused index map of `C̃ ∘ P̃_t`: `ν ℓ = σ_t (rnd (tℓ/s))`. -/
def egNu (s t : ℕ) (ℓ : ℕ) : ℕ := egSigT s t (egRho s t ℓ)

/-- Read a vector at a natural index (`(0,0)` outside). -/
def egGet {n : ℕ} (v : Fin n → ℤ × ℤ) (i : ℕ) : ℤ × ℤ := if h : i < n then v ⟨i, h⟩ else (0, 0)

/-- Index reduction modulo `s`. -/
noncomputable def egIdx (s : ℕ) (hs : 0 < s) (n : ℤ) : Fin s := Work.ResMath.modZ s hs n

/-- The destination key of the source element `i` for the fused `C̃ ∘ P̃_t` step; the keys of the
elements that are not selected are `s + i` (they sort after the `s` selected ones). -/
noncomputable def egLam (s t : ℕ) (i : ℕ) : ℕ :=
  if h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i then ((Classical.choose h : Fin s) : ℕ) else s + i

/-- The destination key of the source element `i` for the final `P̃_sᵀ` step: `(t i) mod s`. -/
def egKeyS (s t : ℕ) (i : ℕ) : ℕ := (t * i) % s

/-- Injectivity of `i ↦ (t i) mod s` on `{0,…,s-1}` (`gcd t s = 1`). -/
lemma egKeyS_inj (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) {a b : ℕ} (ha : a < s) (hb : b < s)
    (h : egKeyS s t a = egKeyS s t b) : a = b := by
  have h1 : t * a ≡ t * b [MOD s] := h
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hcop.symm h1) ha hb

/-- Surjectivity of `i ↦ (t i) mod s` on `{0,…,s-1}`. -/
lemma egKeyS_surj (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (j : Fin s) :
    ∃ i : Fin s, egKeyS s t (i : ℕ) = (j : ℕ) := by
  have hinj : Function.Injective (fun i : Fin s => (⟨egKeyS s t (i : ℕ), Nat.mod_lt _ hs⟩ : Fin s)) := by
    intro a b hab
    exact Fin.ext (egKeyS_inj s t hs hcop a.isLt b.isLt (congrArg Fin.val hab))
  have hsurj : Function.Surjective (fun i : Fin s => (⟨egKeyS s t (i : ℕ), Nat.mod_lt _ hs⟩ : Fin s)) :=
    (Finite.injective_iff_surjective).mp hinj
  obtain ⟨i, hi⟩ := hsurj j
  exact ⟨i, by simpa using congrArg Fin.val hi⟩

/-- `γ j`: the source index of the output `j` in the final `P̃_sᵀ` step. -/
noncomputable def egGam (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (j : Fin s) : Fin s :=
  Classical.choose (egKeyS_surj s t hs hcop j)

lemma egGam_spec (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (j : Fin s) :
    egKeyS s t ((egGam s t hs hcop j : Fin s) : ℕ) = (j : ℕ) :=
  Classical.choose_spec (egKeyS_surj s t hs hcop j)

/-! ## The E-round and the full map -/

/-- The truncated Gaussian convolution `Ẽ` of Lemma 4.11, in exact integer arithmetic. -/
noncomputable def egERound (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ =>
    (Int.tdiv (∑ h ∈ egHset (egM p α),
        egWi p s t α (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).1) ((2 : ℤ) ^ p),
     Int.tdiv (∑ h ∈ egHset (egM p α),
        egWi p s t α (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).2) ((2 : ℤ) ^ p))

/-- The iterates `v^{(j)} = Ẽ^j v`. -/
noncomputable def egIter (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : ℕ → Fin s → ℤ × ℤ
  | 0 => v
  | (j + 1) => egERound p α s t hs (egIter p α s t hs v j)

/-- The alternating (Neumann) sum `Σ_{j<n} (-1)^j v^{(j)}`. -/
noncomputable def egJsum (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ =>
    ((∑ j ∈ Finset.range (egN p α s t), ((-1 : ℤ) ^ j) * (egIter p α s t hs v j ℓ).1),
     (∑ j ∈ Finset.range (egN p α s t), ((-1 : ℤ) ^ j) * (egIter p α s t hs v j ℓ).2))

/-- The `D̃'` scaling. -/
noncomputable def egDsc (p α s t : ℕ) (u : Fin s → ℤ × ℤ) : Fin s → ℤ × ℤ :=
  fun ℓ => (Int.tdiv (egWd p s t α ℓ * (u ℓ).1) ((2 : ℤ) ^ p),
            Int.tdiv (egWd p s t α ℓ * (u ℓ).2) ((2 : ℤ) ^ p))

/-- **The map `Φ = B̃`.** -/
noncomputable def egPhi (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) :
    (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ) :=
  fun w =>
    (let z : Fin s → ℤ × ℤ := fun ℓ => egGet w (egNu s t (ℓ : ℕ))
     let v0 : Fin s → ℤ × ℤ := fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)
     let u := egJsum p α s t hs v0
     let d := egDsc p α s t u
     fun j : Fin s => egGet d ((egGam s t hs hcop j : Fin s) : ℕ))

/-! ## The static table -/

/-- A list of integers as a `Val` (stack of `Val.int`). -/
def zl (l : List ℤ) : Val := HvdH.ofList (l.map Val.int)

/-- The column of rounded weights of the shift `h`. -/
noncomputable def egCol (p s t α : ℕ) (h : ℤ) : Val :=
  zl (List.ofFn (fun ℓ : Fin s => egWi p s t α (ℓ : ℤ) h))

/-- The static table `P` of the resampling word: `[p, α, s, t, m, n, c-keys, s-keys, Dw, cols, signs]`. -/
noncomputable def egTabList (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) : List Val :=
  [ .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
    .int ((egN p α s t : ℕ) : ℤ),
    zl (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ))),
    zl (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ))),
    zl (List.ofFn (fun i : Fin s => egWd p s t α i)),
    ofList ((egHs (egM p α)).map (fun h => Val.cons (.int h) (egCol p s t α h))),
    zl ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1))) ]

/-- The cost shape of the one-dimensional resampling words: one `self`-multiplication budget
`K·t·√p·α·Cm(Kp)` plus one low-level pass `K·t·p²`. -/
def egCostShape (Kc p α t : ℕ) (Cm : ℕ → ℕ) : ℕ :=
  Kc * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kc * p) + p + 1) +
    Kc * (t + 1) * (p + 1) ^ 2

end Work.Resample
