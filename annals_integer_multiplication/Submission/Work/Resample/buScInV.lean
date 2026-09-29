import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample
open HvdH

/-!
# In-disc preservation of the scaling stage (`Work.Resample.buScInV`)

Supporting lemmas (list-level, no programs): the pointwise map

`z ↦ (tdiv (W·z₁) 2^p, tdiv (W·z₂) 2^p)`

with `8|W| ≤ 3·2^p` maps the disc of radius `2^(p+1)` into the disc of radius `2^p`, because
`64(X² + Y²) ≤ 9·4^(p+1) = 36·4^p`, i.e. `X² + Y² ≤ (9/16)·4^p ≤ 4^p`; this applies entrywise to
`buDscL`.  A gather `buPermL` -- an `ofFn` of `getD`s -- trivially keeps the disc.
-/

/-- **Element-level estimate.**  If `8|W| ≤ 3·2^p` and `z` lies in the disc of radius `2^(p+1)`,
then the truncated division `(W·z₁)/2^p`, `(W·z₂)/2^p` (with the *sum of squares*) lies in the disc
of radius `2^p`.  Note that the two coordinates are NOT bounded by `2^p` separately. -/
theorem buIn_tdiv (p : ℕ) (W : ℤ) (z : ℤ × ℤ) (hW : 8 * W.natAbs ≤ 3 * 2 ^ p)
    (hz : buIn (2 ^ (p + 1)) z) :
    buIn (2 ^ p) (Int.tdiv (W * z.1) ((2 : ℤ) ^ p), Int.tdiv (W * z.2) ((2 : ℤ) ^ p)) := by
  -- Real bound for the first coordinate: `|tdiv (W z₁) 2^p| ≤ (3/8)·|z₁|`.
  have hWl : ((Int.tdiv (W * z.1) ((2:ℤ)^p)).natAbs : ℝ) ≤ ((3:ℝ)/8) * (z.1.natAbs : ℝ) := by
    have han : (Int.tdiv (W * z.1) ((2 : ℤ) ^ p)).natAbs = W.natAbs * z.1.natAbs / 2 ^ p := by
      rw [Int.natAbs_tdiv, Int.natAbs_mul, Int.natAbs_pow]; norm_num; exact rfl
    rw [han]
    have hC : (0:ℝ) < (2:ℝ)^p := by positivity
    have hW8 : (8:ℝ) * (W.natAbs:ℝ) ≤ 3 * (2:ℝ)^p := by
      have h' : (8 : ℝ) * (W.natAbs : ℝ) ≤ 3 * (((2^p : ℕ) : ℝ)) := by exact_mod_cast hW
      simpa using h'
    have key : (8:ℝ) * (W.natAbs:ℝ) * (z.1.natAbs:ℝ) ≤ 3 * (2:ℝ)^p * (z.1.natAbs:ℝ) :=
      mul_le_mul_of_nonneg_right hW8 (Nat.cast_nonneg z.1.natAbs)
    have step1 : ((W.natAbs * z.1.natAbs / 2^p : ℕ) : ℝ)
        ≤ ((W.natAbs * z.1.natAbs : ℕ) : ℝ) / (2:ℝ)^p := by
      have h := Nat.cast_div_le (α := ℝ) (m := W.natAbs * z.1.natAbs) (n := 2^p)
      simpa using h
    have step2 : ((W.natAbs * z.1.natAbs : ℕ) : ℝ) / (2:ℝ)^p ≤ ((3:ℝ)/8) * (z.1.natAbs : ℝ) := by
      rw [div_le_iff₀ (G₀ := ℝ) hC]
      push_cast
      linarith [key]
    linarith [step1, step2]
  -- Real bound for the second coordinate.
  have hWr : ((Int.tdiv (W * z.2) ((2:ℤ)^p)).natAbs : ℝ) ≤ ((3:ℝ)/8) * (z.2.natAbs : ℝ) := by
    have han : (Int.tdiv (W * z.2) ((2 : ℤ) ^ p)).natAbs = W.natAbs * z.2.natAbs / 2 ^ p := by
      rw [Int.natAbs_tdiv, Int.natAbs_mul, Int.natAbs_pow]; norm_num; exact rfl
    rw [han]
    have hC : (0:ℝ) < (2:ℝ)^p := by positivity
    have hW8 : (8:ℝ) * (W.natAbs:ℝ) ≤ 3 * (2:ℝ)^p := by
      have h' : (8 : ℝ) * (W.natAbs : ℝ) ≤ 3 * (((2^p : ℕ) : ℝ)) := by exact_mod_cast hW
      simpa using h'
    have key : (8:ℝ) * (W.natAbs:ℝ) * (z.2.natAbs:ℝ) ≤ 3 * (2:ℝ)^p * (z.2.natAbs:ℝ) :=
      mul_le_mul_of_nonneg_right hW8 (Nat.cast_nonneg z.2.natAbs)
    have step1 : ((W.natAbs * z.2.natAbs / 2^p : ℕ) : ℝ)
        ≤ ((W.natAbs * z.2.natAbs : ℕ) : ℝ) / (2:ℝ)^p := by
      have h := Nat.cast_div_le (α := ℝ) (m := W.natAbs * z.2.natAbs) (n := 2^p)
      simpa using h
    have step2 : ((W.natAbs * z.2.natAbs : ℕ) : ℝ) / (2:ℝ)^p ≤ ((3:ℝ)/8) * (z.2.natAbs : ℝ) := by
      rw [div_le_iff₀ (G₀ := ℝ) hC]
      push_cast
      linarith [key]
    linarith [step1, step2]
  -- The hypothesis `a² + b² ≤ 4^(p+1)` as a real statement.
  have hzR : (z.1.natAbs : ℝ)^2 + (z.2.natAbs : ℝ)^2 ≤ (2 * ((2^p : ℕ) : ℝ))^2 := by
    have h1 : ((z.1.natAbs : ℤ))^2 + ((z.2.natAbs : ℤ))^2 ≤ ((2^(p+1) : ℕ) : ℤ)^2 := by
      have h := hz; rw [buIn] at h
      rw [← Int.natAbs_sq z.1, ← Int.natAbs_sq z.2] at h
      exact h
    have h2 : ((z.1.natAbs : ℝ))^2 + ((z.2.natAbs : ℝ))^2 ≤ (((2^(p+1) : ℕ) : ℝ))^2 := by
      exact_mod_cast h1
    have h3 : (((2^(p+1) : ℕ) : ℝ)) = 2 * ((2^p : ℕ) : ℝ) := by push_cast; ring
    rwa [h3] at h2
  set K : ℝ := ((2^p : ℕ) : ℝ) with hKdef
  have hxz : ((Int.tdiv (W * z.1) ((2:ℤ)^p)).natAbs : ℝ)^2
      ≤ (((3:ℝ)/8) * (z.1.natAbs : ℝ))^2 := by
    have h0 : (0:ℝ) ≤ (((Int.tdiv (W * z.1) ((2:ℤ)^p)).natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
    simpa [sq] using mul_self_le_mul_self h0 hWl
  have hyz : ((Int.tdiv (W * z.2) ((2:ℤ)^p)).natAbs : ℝ)^2
      ≤ (((3:ℝ)/8) * (z.2.natAbs : ℝ))^2 := by
    have h0 : (0:ℝ) ≤ (((Int.tdiv (W * z.2) ((2:ℤ)^p)).natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
    simpa [sq] using mul_self_le_mul_self h0 hWr
  have hfin : (((Int.tdiv (W * z.1) ((2:ℤ)^p)).natAbs : ℕ) : ℝ)^2
      + (((Int.tdiv (W * z.2) ((2:ℤ)^p)).natAbs : ℕ) : ℝ)^2 ≤ K^2 := by
    have hr : (z.1.natAbs : ℝ)^2 + (z.2.natAbs : ℝ)^2 ≤ (2*K)^2 := by rw [hKdef]; exact hzR
    nlinarith [hxz, hyz, hr]
  have hnat : ((Int.tdiv (W * z.1) ((2:ℤ)^p)).natAbs)^2 + ((Int.tdiv (W * z.2) ((2:ℤ)^p)).natAbs)^2
      ≤ (2^p)^2 := by
    have h := hfin
    rw [hKdef] at h
    exact_mod_cast h
  show (Int.tdiv (W * z.1) ((2:ℤ)^p))^2 + (Int.tdiv (W * z.2) ((2:ℤ)^p))^2 ≤ ((2^p:ℕ):ℤ)^2
  rw [← Int.natAbs_sq (Int.tdiv (W * z.1) ((2:ℤ)^p)),
    ← Int.natAbs_sq (Int.tdiv (W * z.2) ((2:ℤ)^p))]
  exact_mod_cast hnat

/-- Membership in a `List.zip` projects to membership in both factors. -/
theorem bu_mem_zip {α β : Type*} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) : a ∈ l₁ ∧ b ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨List.mem_cons_self .., List.mem_cons_self ..⟩
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- `buDscL` keeps the disc: pointwise application of `buIn_tdiv`. -/
theorem buDscL_inV (p s : ℕ) (Wd : ℤ → ℤ) (u : List (ℤ × ℤ))
    (hwd : ∀ ℓ : ℤ, 8 * (Wd ℓ).natAbs ≤ 3 * 2 ^ p) (hVu : buInV (2^(p+1)) u) :
    buInV (2^p) (buDscL Wd p s u) := by
  intro z hz
  rw [buDscL] at hz
  obtain ⟨a, haz, hza⟩ := List.mem_map.1 hz
  rw [← hza]
  obtain ⟨h1, h2⟩ := bu_mem_zip haz
  obtain ⟨ℓ, hℓ⟩ := List.mem_ofFn.1 h1
  have hkey : 8 * a.1.natAbs ≤ 3 * 2 ^ p := by rw [← hℓ]; exact hwd (ℓ : ℤ)
  exact buIn_tdiv p a.1 a.2 hkey (hVu a.2 h2)

/-- `buPermL` keeps the disc: it is a gather (`ofFn` of `getD`s), and `(0,0)` is in every disc. -/
theorem buPermL_inV (p s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (d : List (ℤ × ℤ))
    (hVd : buInV (2^p) d) : buInV (2^p) (buPermL s t hs hcop d) := by
  intro z hz
  rw [buPermL] at hz
  obtain ⟨j, hj⟩ := List.mem_ofFn.1 hz
  rw [← hj]
  set k := ((egGam s t hs hcop j : Fin s) : ℕ) with hk
  rcases lt_or_ge k d.length with hklt | hkge
  · rw [List.getD_eq_getElem d (0,0) hklt]
    exact hVd _ (List.getElem_mem hklt)
  · rw [List.getD_eq_default d (0,0) hkge]
    simp [buIn]

/-- In-disc preservation of the scaling stage: `buDscL` keeps the vector in the disc of radius
`2^p` when the input is in the disc of radius `2^(p+1)` and `8|Wd ℓ| ≤ 3·2^p`; and `buPermL` (a
gather) obviously keeps the disc.  Key estimate for the first part: with `W = |Wd ℓ|`,
`8W ≤ 3·2^p`, `X = |tdiv (W a) 2^p| ≤ W|a|/2^p`, `Y ≤ W|b|/2^p` and `a² + b² ≤ 4^(p+1)` one gets
`64(X² + Y²) ≤ 9·4^(p+1) = 36·4^p`, so `X² + Y² ≤ (9/16)·4^p ≤ 4^p`.  (Do NOT try to bound the two
coordinates separately: `3/4·2^p` in each coordinate is too much, the sum of squares is what
closes.) -/
theorem buScInV (p s t : ℕ) (hs : 2 ≤ s) (hcop : Nat.Coprime s t) (Wd : ℤ → ℤ) (u d : List (ℤ × ℤ))
    (hu : u.length = s) (hwd : ∀ ℓ : ℤ, 8 * (Wd ℓ).natAbs ≤ 3 * 2 ^ p)
    (hVu : buInV (2 ^ (p + 1)) u)
    (hd : d.length = s) (hVd : buInV (2 ^ p) d) :
    buInV (2 ^ p) (buDscL Wd p s u) ∧ buInV (2 ^ p) (buPermL s t (by omega) hcop.symm d) :=
  ⟨buDscL_inV p s Wd u hwd hVu, buPermL_inV p s t (by omega) hcop.symm d hVd⟩

end Work.Resample
