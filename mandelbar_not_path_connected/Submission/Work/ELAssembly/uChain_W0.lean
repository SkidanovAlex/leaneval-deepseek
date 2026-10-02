import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELPull.Cert.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## The certificate check `uChain_W0`

The ten arcs `uChainArc i = (aᵢ, bᵢ)` of the `u`-chain certificate are oriented so that the
open counterclockwise arc from `bᵢ` to `aᵢ` (i.e. the *near* arcs of the chain, which wrap
around `0`) contains the whole root arc `(α₁, α₂) = (371/1023, 404/1023)`.

The proof is purely arithmetic about the cyclic arc `Work.EL.InArc`.  We reduce the problem to
three elementary facts about `Int.fract`:

* `InArc` is invariant under shifting the two endpoints by *independent* integers;
* `InArc` is invariant under shifting the angle by an integer;
* an angle strictly inside an unwrapped interval `(a, b)` with `b < a + 1` lies in the arc.

Concretely, for each `i` we exhibit explicit endpoints `p ≤ α₁`, `q ≥ α₂`, `q < p + 1` such
that `p` is `bᵢ` plus an integer and `q` is `aᵢ` plus an integer; then `p < θ < q` for every
angle `θ` of the root arc, which gives `InArc θ p q`, hence `InArc θ bᵢ aᵢ`. -/

/-- `InArc` is invariant under shifting the two endpoints by independent integers. -/
theorem uChain_W0_add_ints (θ a b : ℝ) (p q : ℤ) :
    Work.EL.InArc θ (a + p) (b + q) ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (θ - (a + (p : ℝ))) = Int.fract (θ - a) := by
    have h : θ - (a + (p : ℝ)) = (θ - a) - (p : ℝ) := by ring
    rw [h, Int.fract_sub_intCast]
  have h2 : Int.fract ((b + (q : ℝ)) - (a + (p : ℝ))) = Int.fract (b - a) := by
    have h : (b + (q : ℝ)) - (a + (p : ℝ)) = (b - a) + ((q - p : ℤ) : ℝ) := by
      push_cast; ring
    rw [h, Int.fract_add_intCast]
  rw [h1, h2]

/-- `InArc` is invariant under shifting the angle by an integer. -/
theorem uChain_W0_add_int_theta (θ a b : ℝ) (k : ℤ) :
    Work.EL.InArc (θ + k) a b ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show θ + (k : ℝ) - a = (θ - a) + (k : ℝ) by ring, Int.fract_add_intCast]

/-- An angle strictly inside an *unwrapped* interval `(a, b)` with `b < a + 1` lies in the
open cyclic arc `(a, b)`. -/
theorem uChain_W0_mem_Ioo {a b x : ℝ} (h1 : a < x) (h2 : x < b) (h3 : b < a + 1) :
    Work.EL.InArc x a b := by
  have hx : Int.fract (x - a) = x - a := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hb : Work.EL.arcLen a b = b - a := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [Work.EL.InArc, hx, hb]
  exact ⟨by linarith, by linarith⟩

/-- The core step: if `p ≡ b` and `q ≡ a` modulo `1` and the unwrapped interval `(p, q)` (with
`q < p + 1`) contains the root arc `(371/1023, 404/1023)`, then the near arc `(b, a)` contains
every angle of the root arc. -/
theorem uChain_W0_step {p q : ℝ} (hpq : q < p + 1) (hp : p ≤ 371 / 1023)
    (hq : 404 / 1023 ≤ q) {b a : ℝ} (kb ka : ℤ) (hbp : b + (kb : ℝ) = p)
    (haq : a + (ka : ℝ) = q) (θ : ℝ) (h : Work.EL.InArc θ (371 / 1023) (404 / 1023)) :
    Work.EL.InArc θ b a := by
  obtain ⟨m, hm1, hm2⟩ := Work.ELTop.InArc.exists_int_mem_Ioo
    (a := (371 / 1023 : ℝ)) (b := (404 / 1023 : ℝ)) (by norm_num) h
  have harc : Work.EL.InArc (θ + m) p q := uChain_W0_mem_Ioo (by linarith) (by linarith) hpq
  have h1 : Work.EL.InArc θ p q := (uChain_W0_add_int_theta θ p q m).mp harc
  rw [← hbp, ← haq] at h1
  exact (uChain_W0_add_ints θ b a kb ka).mp h1

theorem uChain_W0 (i : Fin 10) : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ ((Work.ELPull.Cert.uChainArc i).2 : ℝ) ((Work.ELPull.Cert.uChainArc i).1 : ℝ) := by
  fin_cases i <;> intro θ h
  · refine uChain_W0_step (p := 143917 / 523776) (q := 109663 / 523776 + 1)
      (by norm_num) (by norm_num) (by norm_num) 0 1
      (by norm_num [Work.ELPull.Cert.uChainArc_val_0])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_0]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 152225 / 261888 - 1) (q := 117971 / 261888)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_1])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_1]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 143917 / 130944 - 1) (q := 109663 / 130944)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_2])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_2]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 86753 / 65472 - 1) (q := 52499 / 65472)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_3])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_3]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 44191 / 32736 - 1) (q := 12973 / 32736)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_4])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_4]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 4913 / 16368) (q := 3395 / 16368 + 1)
      (by norm_num) (by norm_num) (by norm_num) 0 1
      (by norm_num [Work.ELPull.Cert.uChainArc_val_5])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_5]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 4789 / 8184 - 1) (q := 3271 / 8184)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_6])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_6]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 4913 / 4092 - 1) (q := 3395 / 4092)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_7])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_7]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 2743 / 2046 - 1) (q := 1225 / 2046)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_8])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_8]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h
  · refine uChain_W0_step (p := 1349 / 1023 - 1) (q := 821 / 1023)
      (by norm_num) (by norm_num) (by norm_num) (-1) 0
      (by norm_num [Work.ELPull.Cert.uChainArc_val_9])
      (by norm_num [Work.ELPull.Cert.uChainArc_val_9]) θ ?_
    simpa [Work.EL.alpha1, Work.EL.alpha2] using h

end Work.ELAssembly
