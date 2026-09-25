import Mathlib

/-!
# The anisotropic Littlewood--Paley annuli

Mirek--Stein--Trojan's §6 argument for Theorem 17 decomposes frequency space by the
Littlewood--Paley projections `S_j`, localised on the *anisotropic* annuli
`{ξ : 2^{-1} < |2^{jA}ξ|_∞ < 2}` of the dilation group `A = diag(a_1, …, a_d)`, and then uses two
elementary properties of those annuli to make the sums `Σ_n` over the shifted projections `S_{j+n}`
genuinely summable:

* **bounded overlap** — for `v ≠ 0` the set of levels `m` with `2^{-1} < |2^{mA}v|_∞ < 2` has
  cardinality bounded by a constant depending only on `a` (the map `s ↦ |2^{sA}v|_∞` is monotone in
  `s` and at least doubles when `s ↦ s+1`); hence for each frequency only `O(1)` of the `φ_{j+n}`
  can be nonzero, which is what turns `Σ_n |U_n S_{j+n} f|²` into a genuine square function instead
  of a `√N`-loss over the scale index;
* **scale identification** — if `2^{-1} < |2^{(j+n)A}v|_∞ < 2` then the *unshifted* dilation
  `2^{nA}v` has `∞`-norm between `2^{-1-j·max a}` and `2^{1-j·min a}`; this is what converts the
  pointwise symbol bound `|𝔪_{2^n}(ξ) − m_{2^n}(ξ)| ≲ min{|2^{nA}ξ|_∞, |2^{nA}ξ|_∞^{-1/d}}` into a
  bound geometric in `|j|`, i.e. into the gain `2^{-δ_p |j|}` of MST's `(eq:51)`.

This file only fixes the vocabulary (`anisoDilate`, `anisoSup`, `anisoAmin`, `anisoAmax`,
`anisoAnn`); the two properties themselves are the delegated lemma `anisoAnnulus_facts`.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Maximal

/-- The anisotropic dilation `2^{sA}` with `A = diag(a)`, acting on `ℝ^d`:
`anisoDilate a s v = (2^{s·a_i} · v_i)_i`.  It is the group `s ↦ 2^{sA}` of MST's §6. -/
noncomputable def anisoDilate {d : ℕ} (a : Fin d → ℝ) (s : ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (2 : ℝ) ^ (s * a i) * v i

/-- The anisotropic `∞`-seminorm of the dilated vector, `⨆_i |2^{s·a_i} v_i|` (a finite supremum,
so `sSup` of the range). -/
noncomputable def anisoSup {d : ℕ} (a : Fin d → ℝ) (s : ℝ) (v : Fin d → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin d => |anisoDilate a s v i|)

/-- The smallest exponent of the dilation `A = diag(a)`. -/
noncomputable def anisoAmin {d : ℕ} (a : Fin d → ℝ) : ℝ := sInf (Set.range a)

/-- The largest exponent of the dilation `A = diag(a)`. -/
noncomputable def anisoAmax {d : ℕ} (a : Fin d → ℝ) : ℝ := sSup (Set.range a)

/-- The anisotropic Littlewood--Paley annulus at level `m ∈ ℤ`:
`anisoAnn a m v` says `2^{-1} < ⨆_i |2^{m·a_i} v_i| < 2`. -/
noncomputable def anisoAnn {d : ℕ} (a : Fin d → ℝ) (m : ℤ) (v : Fin d → ℝ) : Prop :=
  (2 : ℝ)⁻¹ < anisoSup a (m : ℝ) v ∧ anisoSup a (m : ℝ) v < 2

end Work.BourgainPlan.Maximal
