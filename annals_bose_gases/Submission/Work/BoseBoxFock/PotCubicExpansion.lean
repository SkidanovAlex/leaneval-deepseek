import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PotCubicPins
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicExpansion` — the four-channel algebraic split of the cubic summand

The pinned modes of the cubic row (`PotCubicPins`) are, by their definitions,

* `pinQ v μ N k y   = (√ℓ³)⁻¹·(e^{i⟪k_m,y⟫}χ_Λ(y) − χ̂(ℓ•k_m)·1_Λ(y))`,  `k_m = kmomLab ℓ N k`,
  `ℓ = ellH v μ` (FS's `qVec`: the localised plane wave with the condensate component removed),
* `pinTheta v μ N s x = (√ℓ³)⁻¹·e^{i⟪s_m,x⟫}1_Λ(x)`,
* `pinCond v μ c x   = c·1_Λ(x)`.

Taking conjugates (`χ_Λ`, `1_Λ` and `χ̂` are real) and multiplying the three factors of the
`cIPn`-integrand gives the **four channels** of FINDING §2 step 3:

    conj(pinQ(s−k) y)·pinTheta s x·conj(pinQ k u) = ((√ℓ³)⁻¹)³·[(a) + (b) + (c) + (d)],

where the weight of each channel is a product of a `y`-factor, an `x`-factor and a `u`-factor.
Channel (a) furthermore **factorises in `(s,k)`**,
`e^{i⟪s,x−y⟫}·e^{i⟪k,y−u⟫}·χ_Λ(y)χ_Λ(x)χ_Λ(u)`, which is what lets the `s`-sum (`Q_L`-frame,
`f_L`-symbol) and the `k`-sum (`w₁`-frame, `Ŵ₁`-symbol) be evaluated independently; channels
(b), (c), (d) carry the `χ̂`-weights and give the `aP`/`aQ` (`θ`-projection) structure of the word.

Nothing here involves the state, the box or the metric: it is the algebraic core of the row's
assembly, independent of how the lattice sums are evaluated (FINDING §5 item 2).
-/

noncomputable section

namespace Work.BoseBoxFock

open Work.BoseB4

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- `1_Λ` is real, hence conjugation-invariant.

⚠ NAME: `conj_thetaFun_self`, not `conj_thetaFun` — the latter is *already* declared in
`Submission/Work/BoseBoxFock/ReflSymm.lean` with a different statement
(`conj (θ (-x)) = θ x`).  The two cones are combined in `PotCubicFree_exists`'s cone (which
contains `ReflSymm` via `PotCubicResiduals`), so the duplicate had to be renamed; this was the
one blocker preventing the `Middle_expansion` layer from coexisting with the target's cone. -/
theorem conj_thetaFun_self (ℓ : ℝ) (x : Ω) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x)
      = Work.BoseK15.corpusBox.thetaFun ℓ x := by
  unfold BoxData.thetaFun
  split <;> simp

/-- **The conjugate of a plane-wave phase.**  `conj (e^{i⟪k,y⟫}) = e^{−i⟪k,y⟫}`. -/
theorem conj_phase (k y : Ω) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ k y : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `χ_Λ` is real, so the conjugate of the localised plane wave is the plane wave with the
opposite frequency times `χ_Λ`.

⚠ NAME: `conj_modeVec_self`, not `conj_modeVec` (declared, with a different statement, in
`Submission/Work/BoseBoxFock/ReflSymm.lean`); see `conj_thetaFun_self`. -/
theorem conj_modeVec_self (ℓ : ℝ) (k y : Ω) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k y)
      = Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
          * ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ) := by
  unfold BoxData.modeVec
  rw [map_mul, conj_phase]
  simp

/-- FS's `qVec` expanded with the conjugate on the outside: the localised plane wave with the
condensate component `χ̂(ℓ•k)·1_Λ` removed (`χ̂` is real). -/
theorem conj_qVec_eq (ℓ : ℝ) (k y : Ω) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k y)
      = Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
          - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y := by
  unfold BoxData.qVec
  rw [map_sub, map_mul, conj_modeVec_self]
  simp [Complex.conj_ofReal, conj_thetaFun_self]

/-- The conjugate of the pinned `χ`-mode `pinQ`, expanded into the `χ_Λ`-part (the localised plane
wave) and the `θ`-part (the removed condensate component). -/
theorem conj_pinQ_eq (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) (y : Ω) :
    (starRingEnd ℂ) (pinQ v μ N k y)
      = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
          (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
            - ((Work.BoseK15.corpusBox.hatChi
                  ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y) := by
  unfold pinQ
  rw [map_mul, conj_qVec_eq]
  simp [Complex.conj_ofReal]

/-- The pinned `θ`-mode `pinTheta`, expanded. -/
theorem pinTheta_eq_exp (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) (x : Ω) :
    pinTheta v μ N s x
      = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x) := by
  unfold pinTheta
  rw [BoxData.thetaExp]

open Classical in
/-- **The four-channel split of the cubic summand.**  Writing `χ` for `chiLam`, `θ` for `thetaFun`
and `χ̂(m)` for `hatChi (ℓ•m)`, the product of the three pinned factors is `((√ℓ³)⁻¹)³` times

* (a) `e^{−i⟪s−k,y⟫}χ(y)·e^{i⟪s,x⟫}θ(x)·e^{−i⟪k,u⟫}χ(u)`,
* (b) `−e^{−i⟪s−k,y⟫}χ(y)·e^{i⟪s,x⟫}θ(x)·χ̂(k)θ(u)`,
* (c) `−χ̂(s−k)θ(y)·e^{i⟪s,x⟫}θ(x)·e^{−i⟪k,u⟫}χ(u)`,
* (d) `+χ̂(s−k)θ(y)·e^{i⟪s,x⟫}θ(x)·χ̂(k)θ(u)`.

Each is a product of a `y`-factor, an `x`-factor and a `u`-factor (`(c)`, `(d)` carry the shifted
weight `χ̂(s−k)`, which couples `s` and `k` — the `aQ`-structure of the word). -/
theorem summand_four_split (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s k : Lab N) (y x u : Ω) :
    (starRingEnd ℂ) (pinQ v μ N (s - k) y) * pinTheta v μ N s x
        * (starRingEnd ℂ) (pinQ v μ N k u)
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3 *
          ( Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)))
                * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))
            - Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)
            - ((Work.BoseK15.corpusBox.hatChi
                  ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)))
                * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))
            + ((Work.BoseK15.corpusBox.hatChi
                  ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)) := by
  rw [conj_pinQ_eq, pinTheta_eq_exp, conj_pinQ_eq]
  ring

end Work.BoseBoxFock
