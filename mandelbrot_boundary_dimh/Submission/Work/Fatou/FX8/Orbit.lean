import Submission.Work.Fatou.FX8.FatouCoord
import Submission.Work.Fatou.Surface.orbitDefs

/-!
# FX8, step 4: the orbit relation A.2.1(i) for the constructed coordinate

For the constructed coordinate `Φ = Ψ ∘ Π / b` the orbit relation holds: if `Φ z' = Φ z + k`
(`k : ℕ`) with `z, z' ∈ Qreg b₁ b₂`, then `z' = F^[k] z` and all intermediate iterates lie in
`Qreg b₁ b₂`.

The proof goes through the sheet structure of `OrbitData`: the equality `Φ z' = Φ z + k` forces
`Π z' = Π z + k`, hence (by `Pi_inj`-style real-part counting) `rep z' = rep z` and
`lev z' = lev z + k`; two points with the same representative are linked by the corresponding
iterate of `F` (`sheet_iterate`), which is the conclusion.
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

open Work.Fatou

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- If `ζ' = ζ + d` with `d : ℤ` and both `ζ, ζ'` are canonical parameters of points of the
fundamental strip, then `d = 0` and the points are equal. -/
theorem canonParam_add_int (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    {s s' : ℂ} (hs : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂))
    (hs' : s' ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)) {d : ℤ}
    (h : canonParam hadm hF s = canonParam hadm hF s' + (d : ℂ)) : d = 0 ∧ s = s' := by
  have hspec := canonParam_spec hadm hF hs
  have hspec' := canonParam_spec hadm hF hs'
  have hre : (canonParam hadm hF s).re = (canonParam hadm hF s').re + (d : ℝ) := by
    have h' := congrArg Complex.re h
    simpa only [Complex.add_re, Complex.intCast_re] using h'
  have hdcast : (d : ℝ) = ((d : ℤ) : ℝ) := rfl
  have hlt : (d : ℝ) < 1 := by have := hspec.2.1; have := hspec'.1; linarith
  have hgt : (-1 : ℝ) < (d : ℝ) := by have := hspec.1; have := hspec'.2.1; linarith
  have hd0 : d = 0 := by
    have h1 : d < 1 := by exact_mod_cast hlt
    have h2 : -1 < d := by exact_mod_cast hgt
    omega
  refine ⟨hd0, ?_⟩
  have hζ : canonParam hadm hF s = canonParam hadm hF s' := by
    rw [h, hd0]; simp
  exact canonParam_inj hadm hF hs hs' hζ

/-- The level of the `k`-th iterate along an orbit piece. -/
theorem lev_iterate (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {z : ℂ} {k : ℕ} (hp : ∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) :
    od.lev (F^[k] z) = od.lev z + (k : ℤ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hp1 : ∀ j ≤ n, F^[j] z ∈ Qreg b₁ b₂ := fun j hj => hp j (le_trans hj (Nat.le_succ n))
    have hmem : F^[n] z ∈ Qreg b₁ b₂ := hp n (Nat.le_succ n)
    have hmem' : F (F^[n] z) ∈ Qreg b₁ b₂ := by
      have := hp (n + 1) le_rfl
      rwa [Function.iterate_succ_apply'] at this
    have hstep := (od.rep_step (F^[n] z) hmem hmem').2
    have hih := ih hp1
    rw [Function.iterate_succ_apply']
    rw [hstep, hih]
    push_cast
    ring

/-- The representative of the `k`-th iterate along an orbit piece. -/
theorem rep_iterate (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {z : ℂ} {k : ℕ} (hp : ∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) :
    od.rep (F^[k] z) = od.rep z := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hp1 : ∀ j ≤ n, F^[j] z ∈ Qreg b₁ b₂ := fun j hj => hp j (le_trans hj (Nat.le_succ n))
    have hmem : F^[n] z ∈ Qreg b₁ b₂ := hp n (Nat.le_succ n)
    have hmem' : F (F^[n] z) ∈ Qreg b₁ b₂ := by
      have := hp (n + 1) le_rfl
      rwa [Function.iterate_succ_apply'] at this
    have hstep := (od.rep_step (F^[n] z) hmem hmem').1
    have hih := ih hp1
    rw [Function.iterate_succ_apply']
    rw [hstep, hih]

/-- **A point of `Qreg` with nonnegative level is a forward iterate of its representative.** -/
theorem sheet_nonneg (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (h : 0 ≤ od.lev z) :
    ∃ j : ℕ, od.lev z = (j : ℤ) ∧ F^[j] (od.rep z) = z ∧
      ∀ i ≤ j, F^[i] (od.rep z) ∈ Qreg b₁ b₂ := by
  obtain ⟨k, hcase⟩ := od.orbit z hz
  rcases hcase with ⟨hfin, hp⟩ | ⟨hfin, hp⟩
  · -- `F^[k] z = rep z`
    have hlev : od.lev (F^[k] z) = od.lev z + (k : ℤ) := lev_iterate hadm hF od hp
    rw [hfin] at hlev
    have hrep : od.rep (od.rep z) = od.rep z ∧ od.lev (od.rep z) = 0 :=
      od.rep_self (od.rep z) (od.rep_mem z hz).1 (od.rep_mem z hz)
    rw [hrep.2] at hlev
    have hlev0 : od.lev z = 0 := by omega
    have hk0 : k = 0 := by omega
    have hrepz : od.rep z = z := by
      have := hfin
      rw [hk0] at this
      simpa using this.symm
    refine ⟨0, by simpa [hlev0], ?_, ?_⟩
    · simpa [hrepz]
    · intro i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simpa using (od.rep_mem z hz).1
  · -- `F^[k] (rep z) = z`
    have hrep : od.rep (od.rep z) = od.rep z ∧ od.lev (od.rep z) = 0 :=
      od.rep_self (od.rep z) (od.rep_mem z hz).1 (od.rep_mem z hz)
    have hlev : od.lev (F^[k] (od.rep z)) = od.lev (od.rep z) + (k : ℤ) := lev_iterate hadm hF od hp
    rw [hfin, hrep.2] at hlev
    exact ⟨k, by simpa using hlev, hfin, hp⟩

/-- **A point of `Qreg` with negative level is a backward iterate of its representative.** -/
theorem sheet_neg (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (h : od.lev z < 0) :
    ∃ j : ℕ, od.lev z = -(j : ℤ) ∧ F^[j] z = od.rep z ∧
      ∀ i ≤ j, F^[i] z ∈ Qreg b₁ b₂ := by
  obtain ⟨k, hcase⟩ := od.orbit z hz
  rcases hcase with ⟨hfin, hp⟩ | ⟨hfin, hp⟩
  · have hlev : od.lev (F^[k] z) = od.lev z + (k : ℤ) := lev_iterate hadm hF od hp
    rw [hfin] at hlev
    have hrep : od.rep (od.rep z) = od.rep z ∧ od.lev (od.rep z) = 0 :=
      od.rep_self (od.rep z) (od.rep_mem z hz).1 (od.rep_mem z hz)
    rw [hrep.2] at hlev
    refine ⟨k, by omega, hfin, hp⟩
  · exfalso
    have hrep : od.rep (od.rep z) = od.rep z ∧ od.lev (od.rep z) = 0 :=
      od.rep_self (od.rep z) (od.rep_mem z hz).1 (od.rep_mem z hz)
    have hlev : od.lev (F^[k] (od.rep z)) = od.lev (od.rep z) + (k : ℤ) := lev_iterate hadm hF od hp
    rw [hfin, hrep.2] at hlev
    omega

/-- **Two points of `Qreg` with the same representative are linked by an iterate of `F`.**
If `lev u ≤ lev v` and `rep u = rep v` then `v = F^[lev v - lev u] u`, with the whole orbit piece
inside `Qreg`. -/
theorem sheet_iterate (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {u v : ℂ} (hu : u ∈ Qreg b₁ b₂) (hv : v ∈ Qreg b₁ b₂)
    (hrep : od.rep u = od.rep v) (hlev : od.lev u ≤ od.lev v) :
    F^[((od.lev v - od.lev u).toNat)] u = v ∧
      ∀ i ≤ ((od.lev v - od.lev u).toNat), F^[i] u ∈ Qreg b₁ b₂ := by
  by_cases ha : 0 ≤ od.lev u
  · -- both levels nonnegative
    obtain ⟨j₁, hj₁, hf₁, hp₁⟩ := sheet_nonneg hadm hF od hu ha
    obtain ⟨j₂, hj₂, hf₂, hp₂⟩ := sheet_nonneg hadm hF od hv (le_trans ha hlev)
    have hK : ((od.lev v - od.lev u).toNat) = j₂ - j₁ := by omega
    refine ⟨?_, ?_⟩
    · rw [hK]
      have h1 : F^[j₂ - j₁] u = F^[j₂] (od.rep v) := by
        rw [← hf₁, hrep, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      rw [h1, hf₂]
    · intro i hi
      rw [hK] at hi
      have h1 : F^[i] u = F^[i + j₁] (od.rep v) := by
        rw [← hf₁, hrep, ← Function.iterate_add_apply]
      rw [h1]
      exact hp₂ (i + j₁) (by omega)
  · have ha' : od.lev u < 0 := lt_of_not_ge ha
    by_cases hb : 0 ≤ od.lev v
    · -- `lev u < 0 ≤ lev v`
      obtain ⟨j₁, hj₁, hf₁, hp₁⟩ := sheet_neg hadm hF od hu ha'
      obtain ⟨j₂, hj₂, hf₂, hp₂⟩ := sheet_nonneg hadm hF od hv hb
      have hK : ((od.lev v - od.lev u).toNat) = j₂ + j₁ := by omega
      refine ⟨?_, ?_⟩
      · rw [hK, Function.iterate_add_apply, hf₁, hrep, hf₂]
      · intro i hi
        rw [hK] at hi
        by_cases hij : i ≤ j₁
        · exact hp₁ i hij
        · have h2 : j₁ ≤ i := le_of_lt (lt_of_not_ge hij)
          have h1 : F^[i] u = F^[i - j₁] (od.rep v) := by
            have h3 : F^[i] u = F^[(i - j₁) + j₁] u := by rw [Nat.sub_add_cancel h2]
            rw [h3, Function.iterate_add_apply, hf₁, hrep]
          rw [h1]
          exact hp₂ (i - j₁) (by omega)
    · -- both levels negative
      have hb' : od.lev v < 0 := lt_of_not_ge hb
      obtain ⟨j₁, hj₁, hf₁, hp₁⟩ := sheet_neg hadm hF od hu ha'
      obtain ⟨j₂, hj₂, hf₂, hp₂⟩ := sheet_neg hadm hF od hv hb'
      have hK : ((od.lev v - od.lev u).toNat) = j₁ - j₂ := by omega
      have hpiecev : Work.Fatou.Surface.Piece b₁ b₂ F v j₂ := hp₂
      have hpieceu : Work.Fatou.Surface.Piece b₁ b₂ F (F^[j₁ - j₂] u) j₂ := by
        intro i hi
        have h1 : F^[i] (F^[j₁ - j₂] u) = F^[i + (j₁ - j₂)] u := by
          rw [Function.iterate_add_apply]
        rw [h1]
        exact hp₁ (i + (j₁ - j₂)) (by omega)
      have heq : F^[j₂] (F^[j₁ - j₂] u) = F^[j₂] v := by
        rw [← Function.iterate_add_apply, show j₂ + (j₁ - j₂) = j₁ by omega, hf₁, hrep, hf₂]
      have hfin : F^[j₁ - j₂] u = v :=
        Work.Fatou.Surface.iter_injOn hadm hF hpieceu hpiecev heq
      refine ⟨?_, ?_⟩
      · rw [hK]; exact hfin
      · intro i hi
        rw [hK] at hi
        exact hp₁ i (by omega)

/-- **The orbit relation A.2.1(i) for the constructed coordinate `Φ`.** -/
theorem Phi_orbit {b : ℂ} (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b) (hb : b ≠ 0)
    {z z' : ℂ} (hz : z ∈ Qreg b₁ b₂) (hz' : z' ∈ Qreg b₁ b₂) (k : ℕ)
    (h : Phi hadm hF od Ψ b z' = Phi hadm hF od Ψ b z + (k : ℂ)) :
    (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∧ F^[k] z = z' := by
  -- multiply the equality by `b`
  have hb' : Ψ ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z'))
      = Ψ ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)) + (k : ℂ) * b := by
    have h2 := congrArg (fun t : ℂ => t * b) h
    simp only [Phi_apply] at h2
    rw [div_mul_cancel₀ _ hb, add_mul, div_mul_cancel₀ _ hb] at h2
    exact h2
  -- rewrite the right-hand side as a deck shift
  have hstep : Ψ ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z'))
      = Ψ (Tpow (fatouData b₁ b₂ F hadm hF) (k : ℤ)
          ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z))) := by
    rw [shift_Tpow (D := fatouData b₁ b₂ F hadm hF) hshift (k : ℤ)
      ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z))]
    rw [hb']
    push_cast
    ring
  have hof : (fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z')
      = Tpow (fatouData b₁ b₂ F hadm hF) (k : ℤ)
          ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)) := Ψ.injective hstep
  have hPi : Pi hadm hF od z' = Pi hadm hF od z + (k : ℂ) := by
    have h3 := congrArg (fun u => (fatouData b₁ b₂ F hadm hF).toℂ u) hof
    simpa using h3
  -- read off representative and level
  have hmain : canonParam hadm hF (od.rep z') + ((od.lev z' : ℤ) : ℂ)
      = canonParam hadm hF (od.rep z) + ((od.lev z : ℤ) : ℂ) + (k : ℂ) := by
    simpa only [Pi] using hPi
  have hkey : canonParam hadm hF (od.rep z')
      = canonParam hadm hF (od.rep z) + (((od.lev z + (k : ℤ)) - od.lev z' : ℤ) : ℂ) := by
    have hcast : (((od.lev z + (k : ℤ)) - od.lev z' : ℤ) : ℂ)
        = (od.lev z : ℂ) + (k : ℂ) - (od.lev z' : ℂ) := by push_cast; ring
    rw [hcast]
    linear_combination hmain
  obtain ⟨hd0, hrep⟩ :=
    canonParam_add_int hadm hF (od.rep_mem z' hz') (od.rep_mem z hz) hkey
  have hlev : od.lev z' = od.lev z + (k : ℤ) := by omega
  have hle : od.lev z ≤ od.lev z' := by omega
  obtain ⟨hfin, hpiece⟩ := sheet_iterate hadm hF od hz hz' hrep.symm hle
  have htoNat : ((od.lev z' - od.lev z).toNat) = k := by omega
  refine ⟨?_, ?_⟩
  · intro j hj
    exact hpiece j (by omega)
  · rw [← htoNat]
    exact hfin

end

end Work.Fatou.FX8
