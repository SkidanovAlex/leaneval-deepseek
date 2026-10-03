import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.Prop172Classical
import Submission.Work.FIArea7.sameClass8_decomp
import Submission.Work.FIArea7.angTrunc_le
import Submission.Work.FIArea4.arg_sub_bounds
import Submission.Work.FIArea7.angFourierCoeff_l1_le
import Submission.Work.FIArea7.cls8_indicator_mul_radBeta

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary helpers of the §17 bridge -/

/-- `radBeta` can only be nonzero at a primary `z`. -/
lemma radBeta_ne_zero_isPrimary {Pa : Work.FITop.Params} {p : ℝ → ℝ} {z : GaussianInt}
    (h : Work.FIArea7.radBeta Pa p Pa.C z ≠ 0) : Work.FIPlan.IsPrimary z := by
  by_contra hc
  rw [Work.FIArea7.radBeta, if_neg (fun hcon => hc hcon.1)] at h
  exact h rfl

/-- A `z` at which `radBeta` does not vanish has nonvanishing complex image. -/
lemma radBeta_ne_zero_toComplex_ne_zero {Pa : Work.FITop.Params} {p : ℝ → ℝ} {z : GaussianInt}
    (h : Work.FIArea7.radBeta Pa p Pa.C z ≠ 0) : z.toComplex ≠ 0 := by
  have hisp := radBeta_ne_zero_isPrimary h
  obtain ⟨hodd, -, -⟩ := hisp
  have hre : z.re ≠ 0 := by
    intro h0
    rw [h0] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega
  have hz : z ≠ 0 := fun h0 => hre (by rw [h0]; simp)
  exact Work.FIArea7.LogFacArg.toComplex_ne_zero_of_gnorm_pos
    (Work.FIArea7.LogFacArg.gnorm_pos_of_ne_zero hz)

/-! ## 1. `uniPow` as an exponential -/

/-- For `z ≠ 0`, `(z/|z|)^k = e^{ik·arg z}`. -/
lemma uniPow_eq_exp {z : GaussianInt} (hz : z.toComplex ≠ 0) (k : ℤ) :
    Work.FIArea7.uniPow z k = Complex.exp (Complex.I * (k : ℂ) * (z.toComplex.arg : ℂ)) := by
  have hbase : z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)
      = Complex.exp (Complex.I * (z.toComplex.arg : ℂ)) := by
    have hrne : ((‖z.toComplex‖ : ℝ) : ℂ) ≠ 0 := by simp [hz]
    rw [div_eq_iff hrne, mul_comm]
    rw [show Complex.exp (Complex.I * (z.toComplex.arg : ℂ))
          = Complex.exp ((z.toComplex.arg : ℂ) * Complex.I) from by ring_nf]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.re_add_im z.toComplex]
    simp
  rw [Work.FIArea7.uniPow, hbase, ← Complex.exp_int_mul]
  ring_nf

/-- The mode-combination identity: `(z/|z|)^k · e^{iℓ(arg z − φ)} = e^{−iℓφ}(z/|z|)^{k+ℓ}`. -/
lemma uniPow_mul_exp {z : GaussianInt} (hz : z.toComplex ≠ 0) (k ℓ : ℤ) (φ : ℝ) :
    Work.FIArea7.uniPow z k
        * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ))
      = Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ))) * Work.FIArea7.uniPow z (k + ℓ) := by
  rw [uniPow_eq_exp hz k, uniPow_eq_exp hz (k + ℓ)]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The mode-combination identity multiplied by an arbitrary factor. -/
lemma uniPow_mul_exp_mul (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z : GaussianInt)
    (k ℓ : ℤ) (φ : ℝ) (c : ℂ) :
    (Work.FIArea7.uniPow z k
        * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
        * (Work.FIArea7.radBeta Pa p Pa.C z * c)
      = (Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ))) * Work.FIArea7.uniPow z (k + ℓ))
        * (Work.FIArea7.radBeta Pa p Pa.C z * c) := by
  by_cases h : Work.FIArea7.radBeta Pa p Pa.C z = 0
  · simp [h]
  · rw [uniPow_mul_exp (radBeta_ne_zero_toComplex_ne_zero h) k ℓ φ]

/-- The mode-combination identity at the class-restricted coefficient `radBetaCls`. -/
lemma uniPow_mul_exp_radBetaCls (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z0 z : GaussianInt)
    (k ℓ : ℤ) (φ : ℝ) :
    (Work.FIArea7.uniPow z k
        * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
        * Work.FIArea7.radBetaCls Pa p z0 z
      = Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ))) * Work.FIArea7.uniPow z (k + ℓ)
        * Work.FIArea7.radBetaCls Pa p z0 z := by
  rw [Work.FIArea7.radBetaCls]
  rw [mul_comm (if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)
    (Work.FIArea7.radBeta Pa p Pa.C z)]
  exact uniPow_mul_exp_mul Pa p z k ℓ φ
    (if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)

/-! ## 2. Periodicity of the class characters `a_i` -/

/-- An `a` that is `8`-periodic in the real coordinate is periodic under the shift by any
multiple of `8`. -/
lemma a_periodic_re (a : GaussianInt → ℂ) (hA : ∀ z : GaussianInt, a (z + 8) = a z) :
    ∀ (K : ℕ) (m b : ℤ), a (⟨m + 8 * (K : ℤ), b⟩ : GaussianInt) = a (⟨m, b⟩ : GaussianInt) := by
  intro K
  induction K with
  | zero => intro m b; simp
  | succ k ih =>
      intro m b
      have h1 : (⟨m + 8 * (((k : ℕ) + 1 : ℕ) : ℤ), b⟩ : GaussianInt)
          = (⟨m + 8 * (k : ℤ), b⟩ : GaussianInt) + 8 := by
        ext <;> simp <;> ring
      rw [h1, hA]
      exact ih m b

/-- The same for the imaginary coordinate. -/
lemma a_periodic_im (a : GaussianInt → ℂ)
    (hA : ∀ z : GaussianInt, a (⟨z.re, z.im + 8⟩ : GaussianInt) = a z) :
    ∀ (K : ℕ) (m b : ℤ), a (⟨m, b + 8 * (K : ℤ)⟩ : GaussianInt) = a (⟨m, b⟩ : GaussianInt) := by
  intro K
  induction K with
  | zero => intro m b; simp
  | succ k ih =>
      intro m b
      have h1 : (⟨m, b + 8 * (((k : ℕ) + 1 : ℕ) : ℤ)⟩ : GaussianInt)
          = (⟨m, (b + 8 * (k : ℤ)) + 8⟩ : GaussianInt) := by
        ext <;> simp <;> ring
      rw [h1]
      have hstep : a (⟨m, (b + 8 * (k : ℤ)) + 8⟩ : GaussianInt)
          = a (⟨m, b + 8 * (k : ℤ)⟩ : GaussianInt) :=
        hA (⟨m, b + 8 * (k : ℤ)⟩ : GaussianInt)
      rw [hstep, ih m b]

/-- `chiOf` transported and conjugated, the character fed to `Prop172Classical`. -/
noncomputable def chiPrime (Q : ℕ) (χ : AddChar (Additive (GaussUnit Q)) ℂ)
    (a : GaussianInt → ℂ) (z : GaussianInt) : ℂ := star (chiOf Q χ z) * a z

lemma chiPrime_mul (Q : ℕ) [NeZero Q] (χ : AddChar (Additive (GaussUnit Q)) ℂ)
    (a : GaussianInt → ℂ)
    (ha : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → a (z1 * z2) = a z1 * a z2)
    (z1 z2 : GaussianInt) (h : IsCoprime z1 z2) :
    chiPrime Q χ a (z1 * z2) = chiPrime Q χ a z1 * chiPrime Q χ a z2 := by
  rw [chiPrime, chiPrime, chiPrime, chiOf_mul, star_mul, ha z1 z2 h]
  ring

lemma chiPrime_norm_le (Q : ℕ) [NeZero Q] (χ : AddChar (Additive (GaussUnit Q)) ℂ)
    (a : GaussianInt → ℂ) (ha : ∀ z, ‖a z‖ ≤ 1) (z : GaussianInt) :
    ‖chiPrime Q χ a z‖ ≤ 1 := by
  rw [chiPrime, norm_mul]
  calc ‖star (chiOf Q χ z)‖ * ‖a z‖ ≤ 1 * 1 := by
        refine mul_le_mul ?_ (ha z) (norm_nonneg _) (by norm_num)
        rw [norm_star]; exact chiOf_norm_le χ z
    _ = 1 := one_mul 1

lemma chiPrime_periodic_re (Q : ℕ) [NeZero Q] (χ : AddChar (Additive (GaussUnit Q)) ℂ)
    (a : GaussianInt → ℂ) (hA : ∀ z : GaussianInt, a (z + 8) = a z) (m b : ℤ) :
    chiPrime Q χ a (⟨m + 8 * (Q : ℤ), b⟩ : GaussianInt)
      = chiPrime Q χ a (⟨m, b⟩ : GaussianInt) := by
  have hchi : chiOf Q χ (⟨m + 8 * (Q : ℤ), b⟩ : GaussianInt)
      = chiOf Q χ (⟨m, b⟩ : GaussianInt) :=
    chiOf_periodic (n := Q) χ (z := ⟨m + 8 * (Q : ℤ), b⟩) (w := ⟨m, b⟩) (by
      refine ⟨(8 : GaussianInt), ?_⟩
      ext <;> simp <;> ring)
  have ha : a (⟨m + 8 * (Q : ℤ), b⟩ : GaussianInt) = a (⟨m, b⟩ : GaussianInt) :=
    a_periodic_re a hA Q m b
  rw [chiPrime, chiPrime, hchi, ha]

lemma chiPrime_periodic_im (Q : ℕ) [NeZero Q] (χ : AddChar (Additive (GaussUnit Q)) ℂ)
    (a : GaussianInt → ℂ) (hA : ∀ z : GaussianInt, a (⟨z.re, z.im + 8⟩ : GaussianInt) = a z)
    (m b : ℤ) :
    chiPrime Q χ a (⟨m, b + 8 * (Q : ℤ)⟩ : GaussianInt)
      = chiPrime Q χ a (⟨m, b⟩ : GaussianInt) := by
  have hchi : chiOf Q χ (⟨m, b + 8 * (Q : ℤ)⟩ : GaussianInt)
      = chiOf Q χ (⟨m, b⟩ : GaussianInt) :=
    chiOf_periodic (n := Q) χ (z := ⟨m, b + 8 * (Q : ℤ)⟩) (w := ⟨m, b⟩) (by
      refine ⟨(⟨0, 8⟩ : GaussianInt), ?_⟩
      ext <;> simp <;> ring)
  have ha : a (⟨m, b + 8 * (Q : ℤ)⟩ : GaussianInt) = a (⟨m, b⟩ : GaussianInt) :=
    a_periodic_im a hA Q m b
  rw [chiPrime, chiPrime, hchi, ha]


/-! ## 3. The expansion of `star (uniSChar … β_L)` in the angular frequencies -/

/-- Distribute a left factor and two right factors into a finite sum. -/
private lemma mul_sum_mul_mul (A u s : ℂ) (f : ℤ → ℂ) (t : Finset ℤ) :
    A * (∑ ℓ ∈ t, f ℓ) * u * s = ∑ ℓ ∈ t, A * f ℓ * u * s := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]

/-- The `z`-summand of `star (uniSChar …)`, expanded over the `angTruncSum` index. -/
private lemma stepB (R J u s : ℂ) (g : ℤ → ℂ) (t : Finset ℤ) :
    J * ((∑ ℓ ∈ t, g ℓ) * R) * u * s = ∑ ℓ ∈ t, J * g ℓ * R * u * s := by
  rw [Finset.sum_mul, mul_sum_mul_mul]
  exact Finset.sum_congr rfl (fun ℓ _ => by ring)

/-- The commutativity bookkeeping of the mode combination. -/
private lemma stepD_atom (J W e R u U s f : ℂ) (h : (u * e) * R = f * U * R) :
    J * (W * e) * R * u * s = W * f * (J * U * s * R) := by
  have h1 : J * (W * e) * R * u * s = W * (J * ((u * e) * R) * s) := by ring
  rw [h1, h]
  ring

/-- The `z`-sum at a fixed frequency, rewritten through the mode-combination identity. -/
private lemma stepD (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (z0 : GaussianInt) (L : ℕ)
    (k : ℤ) (ℓ : ℤ) (φ : ℝ) (Q : ℕ) [NeZero Q]
    (χ : AddChar (Additive (GaussUnit Q)) ℂ) :
    (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.JKSym z
          * (Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
              * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
          * Work.FIArea7.radBetaCls Pa p z0 z * Work.FIArea7.uniPow z k
          * star (Work.FIArea7.chiOf Q χ z))
      = Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
          * Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))
        * ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ) * star (Work.FIArea7.chiOf Q χ z)
              * Work.FIArea7.radBetaCls Pa p z0 z := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  exact stepD_atom (Work.FIArea7.JKSym z)
    (Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ)
    (Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
    (Work.FIArea7.radBetaCls Pa p z0 z) (Work.FIArea7.uniPow z k) (Work.FIArea7.uniPow z (k + ℓ))
    (star (Work.FIArea7.chiOf Q χ z)) (Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ))))
    (uniPow_mul_exp_radBetaCls Pa p z0 z k ℓ φ)

/-- The conjugate of `uniSChar` at the bridge coefficient, expanded in the angular frequency. -/
private lemma star_uniSChar_expand (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q]
    (q p : ℝ → ℝ) (φ : ℝ) (z0 : GaussianInt) (L : ℕ) (k : ℤ)
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ) :
    star (Work.FIArea7.uniSChar Pa Q (fun _ => 1) (Work.FIArea7.betaL Pa q p φ z0 L) k χ)
      = ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
          Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
            * Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))
            * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ)
                  * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.radBetaCls Pa p z0 z) := by
  have hstar : star (Work.FIArea7.uniSChar Pa Q (fun _ => 1) (Work.FIArea7.betaL Pa q p φ z0 L)
        k χ)
      = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          Work.FIArea7.JKSym z * Work.FIArea7.betaL Pa q p φ z0 L z
            * Work.FIArea7.uniPow z k * star (Work.FIArea7.chiOf Q χ z) := by
    rw [Work.FIArea7.uniSChar, star_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have hc : Work.FIArea7.unitInd Q z
          * star (χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)))
        = star (Work.FIArea7.chiOf Q χ z) := by
      rw [Work.FIArea7.chiOf_eq_unitInd_mul Q χ z, star_mul, star_unitInd]
      ring
    rw [Work.FIArea7.unitCoeff, Work.FIArea7.uniCoeff, Work.FIArea7.betaPrime]
    simp only [Int.cast_one, one_mul]
    rw [star_mul, star_mul, star_unitInd, star_star, ← hc]
    ring
  rw [hstar]
  rw [show (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        Work.FIArea7.JKSym z * Work.FIArea7.betaL Pa q p φ z0 L z
          * Work.FIArea7.uniPow z k * star (Work.FIArea7.chiOf Q χ z))
      = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
          Work.FIArea7.JKSym z
            * (Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
                * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
            * Work.FIArea7.radBetaCls Pa p z0 z * Work.FIArea7.uniPow z k
            * star (Work.FIArea7.chiOf Q χ z) from
    Finset.sum_congr rfl (fun z _ => by
      rw [Work.FIArea7.betaL, Work.FIArea7.angTruncSum]
      exact stepB (Work.FIArea7.radBetaCls Pa p z0 z) (Work.FIArea7.JKSym z)
        (Work.FIArea7.uniPow z k) (star (Work.FIArea7.chiOf Q χ z))
        (fun ℓ => Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
              * Complex.exp (Complex.I * (ℓ : ℂ) * ((z.toComplex.arg - φ : ℝ) : ℂ)))
        (Finset.Icc (-(L : ℤ)) L))]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun ℓ _ => stepD Pa q p z0 L k ℓ φ Q χ)

/-- **A5: *FI* Proposition 17.2 at the shifted frequencies for `betaL`** — this is the point where
the deep input `Prop172Classical` is consumed by area 7 (`AREA7_ROUTE_LEAD.md` §2.2 (A5)).

Proof: (1) expand `angTruncSum`: `e^{iℓ(arg z − φ)} = e^{−iℓφ}(z/|z|)^ℓ`, so the mode becomes
`k + ℓ`; (2) expand the class indicator by `sameClass8_decomp` (32 characters, `‖c‖ ≤ 1`);
(3) transport `χ` by `chiOf_eq_unitInd_mul` — the product `chiOf Q χ · a_i` is multiplicative,
bounded and `8Q = 4·(2Q)`-periodic; (4) conjugate once to get the honest `[z]`, and with `hfar`
the reflection sign is `ε ≡ 1`; (5) apply `Prop172Classical` at `d = 2Q`, `m = k+ℓ`, which needs
`2Q(|k+ℓ|+1) ≤ N^{δ₁}`, ensured by `2Q(|k|+L+1) ≤ N^{δ₁}`; (6) sum `Σ_ℓ|angFourierCoeff| ≤ C`
by (16.26), giving `c₁ := 32·C·c₁^{(17.2)}`. -/
theorem uniSChar_betaL_le (h172 : Work.FIArea7.Prop172Classical) :
  ∀ η : ℝ, 0 < η → η < 3 / 32 → ∃ δ₁ c₁ x0 : ℝ, 0 < δ₁ ∧ 0 < c₁ ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (q p : ℝ → ℝ) (φ : ℝ) (z0 : GaussianInt) (L : ℕ),
    Work.FIArea7.IsMollPair Pa q p →
    -Real.pi ≤ φ → φ ≤ Real.pi - 2 * Real.pi * Pa.θ → 1 ≤ L →
  ∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
    2 * (Q : ℝ) * (|(k:ℝ)| + (L:ℝ) + 1) ≤ Pa.N ^ δ₁ →
    ‖Work.FIArea7.uniSChar Pa Q (fun _ => 1) (Work.FIArea7.betaL Pa q p φ z0 L) k χ‖
      ≤ c₁ * Pa.N ^ (1 - δ₁) := by
  intro η hη hη32
  obtain ⟨δ₁, c₁', x0', hδ₁, hc₁', h172'⟩ := h172 η hη hη32
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea7.angFourierCoeff_l1_le
  obtain ⟨N8, a8, c8, ha8mul, ha8bdd, ha8p1, ha8p2, hc8bdd, hc8pos, hc8neg⟩ :=
    Work.FIArea7.sameClass8_decomp
  refine ⟨δ₁, ((max N8 1 : ℕ) : ℝ) * C1 * c₁', max x0' 3, hδ₁, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((max N8 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N8 1
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one h1) hC1pos) hc₁'
  · intro Pa hx hηPa q p φ z0 L hMoll hφ1 hφ2 hL Q _inst k χ hcond
    have hx' : x0' ≤ (Pa.x : ℝ) := le_trans (le_max_left x0' 3) hx
    have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)
    have hchi : ∀ i : Fin N8,
        (∀ z : GaussianInt, ‖chiPrime Q χ (a8 i) z‖ ≤ 1) ∧
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 →
            chiPrime Q χ (a8 i) (z1 * z2)
              = chiPrime Q χ (a8 i) z1 * chiPrime Q χ (a8 i) z2) ∧
        (∀ a b' : ℤ, chiPrime Q χ (a8 i) (⟨a + 4 * ((2 * Q : ℕ) : ℤ), b'⟩ : GaussianInt)
            = chiPrime Q χ (a8 i) (⟨a, b'⟩ : GaussianInt)) ∧
        (∀ a b' : ℤ, chiPrime Q χ (a8 i) (⟨a, b' + 4 * ((2 * Q : ℕ) : ℤ)⟩ : GaussianInt)
            = chiPrime Q χ (a8 i) (⟨a, b'⟩ : GaussianInt)) := by
      intro i
      refine ⟨chiPrime_norm_le Q χ (a8 i) (ha8bdd i), ?_, ?_, ?_⟩
      · intro z1 z2 h
        exact chiPrime_mul Q χ (a8 i) (ha8mul i) z1 z2 h
      · intro a b'
        rw [show (4 : ℤ) * ((2 * Q : ℕ) : ℤ) = 8 * (Q : ℤ) from by push_cast; ring]
        exact chiPrime_periodic_re Q χ (a8 i) (ha8p1 i) a b'
      · intro a b'
        rw [show (4 : ℤ) * ((2 * Q : ℕ) : ℤ) = 8 * (Q : ℤ) from by push_cast; ring]
        exact chiPrime_periodic_im Q χ (a8 i) (ha8p2 i) a b'
    have hterm : ∀ (ℓ : ℤ) (i : Fin N8), ℓ ∈ Finset.Icc (-(L : ℤ)) L →
        ‖Work.FIArea7.SChiRad Pa p Pa.C (chiPrime Q χ (a8 i)) (k + ℓ)‖
          ≤ c₁' * Pa.N ^ (1 - δ₁) := by
      intro ℓ i hℓ
      have hℓabs : |(ℓ : ℝ)| ≤ (L : ℝ) := by
        rw [Finset.mem_Icc] at hℓ
        rw [abs_le]
        exact ⟨by exact_mod_cast hℓ.1, by exact_mod_cast hℓ.2⟩
      have hcond' : ((2 * Q : ℕ) : ℝ) * (|((k + ℓ : ℤ) : ℝ)| + 1) ≤ Pa.N ^ δ₁ := by
        have h2Q : ((2 * Q : ℕ) : ℝ) = 2 * (Q : ℝ) := by push_cast; ring
        rw [h2Q]
        have hnum : |((k + ℓ : ℤ) : ℝ)| + 1 ≤ |(k : ℝ)| + (L : ℝ) + 1 := by
          have hcast : ((k + ℓ : ℤ) : ℝ) = (k : ℝ) + (ℓ : ℝ) := by push_cast; ring
          rw [hcast]
          have := abs_add_le (k : ℝ) (ℓ : ℝ)
          linarith
        exact le_trans (mul_le_mul_of_nonneg_left hnum (by positivity)) hcond
      have hd1 : 1 ≤ 2 * Q := by omega
      have hC2' : Pa.C ≤ Pa.N ^ (1 - η) := by simpa [hηPa] using Pa.hC2
      exact h172' Pa hx' hηPa p Pa.C (2 * Q) (chiPrime Q χ (a8 i)) (k + ℓ)
        hMoll.2.1 (fun u => (hMoll.2.2.2.2.2.1 u).1) (fun u => (hMoll.2.2.2.2.2.1 u).2)
        hMoll.2.2.2.2.2.2.1 hMoll.2.2.2.2.2.2.2 Pa.hC1 hC2' hd1
        (hchi i).1 (hchi i).2.1 (hchi i).2.2.1 (hchi i).2.2.2 hcond'
    have hM1 := star_uniSChar_expand Pa Q q p φ z0 L k χ
    have hinner : ∀ ℓ : ℤ,
        (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ)
              * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.radBetaCls Pa p z0 z)
          = ∑ i : Fin N8,
              c8 z0 i * Work.FIArea7.SChiRad Pa p Pa.C (chiPrime Q χ (a8 i)) (k + ℓ) :=
      fun ℓ => Work.FIArea7.cls8_indicator_mul_radBeta hc8pos hc8neg Pa p z0 (k + ℓ) Q χ
    have hexp_norm : ∀ ℓ : ℤ, ‖Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))‖ = 1 := by
      intro ℓ
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * (ℓ : ℂ) * (φ : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    have hX : ∀ ℓ : ℤ, ℓ ∈ Finset.Icc (-(L : ℤ)) L →
        ‖∑ i : Fin N8, c8 z0 i * Work.FIArea7.SChiRad Pa p Pa.C (chiPrime Q χ (a8 i)) (k + ℓ)‖
          ≤ (N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁)) := by
      intro ℓ hℓ
      refine le_trans (norm_sum_le _ _) ?_
      have h1 : ∀ i : Fin N8,
          ‖c8 z0 i * Work.FIArea7.SChiRad Pa p Pa.C (chiPrime Q χ (a8 i)) (k + ℓ)‖
            ≤ 1 * (c₁' * Pa.N ^ (1 - δ₁)) := by
        intro i
        rw [norm_mul]
        exact mul_le_mul (hc8bdd i z0) (hterm ℓ i hℓ) (norm_nonneg _) (by norm_num)
      calc ∑ i : Fin N8,
            ‖c8 z0 i * Work.FIArea7.SChiRad Pa p Pa.C (chiPrime Q χ (a8 i)) (k + ℓ)‖
          ≤ ∑ _i : Fin N8, (1 * (c₁' * Pa.N ^ (1 - δ₁))) := Finset.sum_le_sum (fun i _ => h1 i)
        _ = (N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁)) := by simp
    have hsum : ∀ ℓ : ℤ, ℓ ∈ Finset.Icc (-(L : ℤ)) L →
        ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
            * Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))
            * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ)
                  * star (Work.FIArea7.chiOf Q χ z) * Work.FIArea7.radBetaCls Pa p z0 z)‖
          ≤ ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ‖
            * ((N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁))) := by
      intro ℓ hℓ
      rw [hinner ℓ, norm_mul, norm_mul, hexp_norm ℓ, mul_one]
      exact mul_le_mul_of_nonneg_left (hX ℓ hℓ) (norm_nonneg _)
    have hl1 : ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
          ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ‖ ≤ C1 :=
      hC1 q Pa.θ L Pa.hθ0 (le_trans (Work.FIArea4.theta_le_eighth Pa) (by norm_num))
        hMoll.1 hMoll.2.2.1 hMoll.2.2.2.1 hMoll.2.2.2.2.1
    have hXnn : 0 ≤ Pa.N ^ (1 - δ₁) := Real.rpow_nonneg (by linarith [Pa.hN1]) _
    have hN8le : (N8 : ℝ) ≤ ((max N8 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left N8 1
    calc ‖Work.FIArea7.uniSChar Pa Q (fun _ => 1) (Work.FIArea7.betaL Pa q p φ z0 L) k χ‖
        = ‖star (Work.FIArea7.uniSChar Pa Q (fun _ => 1)
              (Work.FIArea7.betaL Pa q p φ z0 L) k χ)‖ := (norm_star _).symm
      _ = ‖∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
              Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
                * Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))
                * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ)
                      * star (Work.FIArea7.chiOf Q χ z)
                      * Work.FIArea7.radBetaCls Pa p z0 z)‖ := by
            rw [hM1]
      _ ≤ ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
              ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
                * Complex.exp (-(Complex.I * (ℓ : ℂ) * (φ : ℂ)))
                * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                    Work.FIArea7.JKSym z * Work.FIArea7.uniPow z (k + ℓ)
                      * star (Work.FIArea7.chiOf Q χ z)
                      * Work.FIArea7.radBetaCls Pa p z0 z)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
              ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ‖
                * ((N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁))) :=
            Finset.sum_le_sum (fun ℓ hℓ => hsum ℓ hℓ)
      _ = (∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
              ‖Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ‖)
            * ((N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁))) := by
            rw [Finset.sum_mul]
      _ ≤ C1 * ((N8 : ℝ) * (c₁' * Pa.N ^ (1 - δ₁))) :=
            mul_le_mul_of_nonneg_right hl1
              (mul_nonneg (Nat.cast_nonneg N8) (mul_nonneg (le_of_lt hc₁') hXnn))
      _ = ((N8 : ℝ) * C1 * c₁') * Pa.N ^ (1 - δ₁) := by ring
      _ ≤ (((max N8 1 : ℕ) : ℝ) * C1 * c₁') * Pa.N ^ (1 - δ₁) := by
            refine mul_le_mul_of_nonneg_right ?_ hXnn
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hN8le (le_of_lt hC1pos)) (le_of_lt hc₁')

end

end Work.FIArea7
