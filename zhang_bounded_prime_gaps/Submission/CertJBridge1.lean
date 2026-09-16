import Submission.CertJData
import Submission.CertJPsiND

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `J`-form as a flat double sum over the certificate data

`certJSum` (the cleared `J` quadratic form of `Submission.CertArith`) is a four-fold sum over
the basis index `j`, the marginal part `v`, and their primed versions.  Here we rewrite it as a
double sum over the flat list `cJTrips` of `(β, ã, W)` triples.

Note that `certJPsiN j v j' v'` depends on `(j,v)` only through `(ã, |β|)`, so the `Ψ`-kernel
is the *sum* `certJPsiND N L`; the table lookup replacing it is in `Submission.CertJBridge2`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The flat `(β, ã, W)` entry of a basis triple `u = (α, a, c)` and a part `v`. -/
def cJEntry (u : List ℕ × ℕ × ℤ) (v : ℕ) : List ℕ × ℕ × ℤ :=
  (eraseOne u.1 v, u.2.1 + v + 1, u.2.2 * (certJKappaD u.2.1 v : ℤ))

/-- The flat entries of one basis triple. -/
def cJFlat (u : List ℕ × ℕ × ℤ) : List (List ℕ × ℕ × ℤ) :=
  (0 :: u.1.dedup).map (fun v => cJEntry u v)

theorem cJTrips_eq_flatMap : cJTrips = cTrips.flatMap cJFlat := rfl

/-- The summand of the four-fold form, in the basis variables. -/
def Gtu (u u' : List ℕ × ℕ × ℤ) (v v' : ℕ) : ℤ :=
  u.2.2 * u'.2.2 * (certJKappaD u.2.1 v : ℤ) * (certJKappaD u'.2.1 v' : ℤ) *
    (Ssum (eraseOne u.1 v) (eraseOne u'.1 v') 49 : ℤ) *
    (certJPsiND ((u.2.1 + v + 1) + (u'.2.1 + v' + 1))
      ((eraseOne u.1 v).sum + (eraseOne u'.1 v').sum) : ℤ)

/-- The flat summand of the `J`-form. -/
def Gt (w w' : List ℕ × ℕ × ℤ) : ℤ :=
  w.2.2 * w'.2.2 * (Ssum w.1 w'.1 49 : ℤ) * (certJPsiND (w.2.1 + w'.2.1) (w.1.sum + w'.1.sum) : ℤ)

theorem Gt_cJEntry (u u' : List ℕ × ℕ × ℤ) (v v' : ℕ) :
    Gt (cJEntry u v) (cJEntry u' v') = Gtu u u' v v' := by
  simp only [Gt, Gtu, cJEntry]; ring

/-- The inner (`v'`) sum of the four-fold form. -/
def cJSumV (u u' : List ℕ × ℕ × ℤ) (v : ℕ) : ℤ :=
  ((0 :: u'.1.dedup).map (fun v' => Gtu u u' v v')).sum

/-- The (`v`,`v'`) sum of the four-fold form. -/
def cJSumU (u u' : List ℕ × ℕ × ℤ) : ℤ := ((0 :: u.1.dedup).map (fun v => cJSumV u u' v)).sum

/-- The four-fold form over the basis triples. -/
def cJSumTrips : ℤ := (cTrips.map (fun u => (cTrips.map (fun u' => cJSumU u u')).sum)).sum

/-- `cJSumU` in terms of the flat entries. -/
theorem cJSumU_eq (u u' : List ℕ × ℕ × ℤ) :
    cJSumU u u' = ((cJFlat u).map (fun w => ((cJFlat u').map (fun w' => Gt w w')).sum)).sum := by
  unfold cJSumU cJSumV cJFlat
  simp only [List.map_map]
  refine congrArg List.sum (List.map_congr_left (fun v _ => ?_))
  exact congrArg List.sum (List.map_congr_left (fun v' _ => (Gt_cJEntry u u' v v').symm))

theorem nodup_cons_dedup (α : List ℕ) (h : 0 ∉ α) : (0 :: α.dedup).Nodup :=
  List.nodup_cons.mpr ⟨fun hm => h (List.mem_dedup.mp hm), List.nodup_dedup α⟩

/-- The membership of the certificate's marginal parts, as a list. -/
theorem sum_toFinset_sig (j : Fin 1780) (f : ℕ → ℤ) :
    (∑ v ∈ (0 :: (certSig j).dedup).toFinset, f v)
      = ((0 :: (certSig j).dedup).map f).sum :=
  List.sum_toFinset f (nodup_cons_dedup _ (certSig_notMem_zero j))

theorem term_eq_Gtu (j : Fin 1780) (v : ℕ) (j' : Fin 1780) (v' : ℕ) :
    certCs j * certCs j' * certJKappaN j v * certJKappaN j' v' *
      (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℤ) * (certJPsiN j v j' v' : ℤ)
    = Gtu (cTrip j) (cTrip j') v v' := by
  unfold Gtu cTrip certJKappaD certJKappaN certJKappaN' certJBeta certJPsiN certJPsiND
    certJN certJLM certJExp
  rfl

/-- The four-fold form, as a sum over the basis triples and their parts. -/
theorem certJSum_double : certJSum = cJSumTrips := by
  unfold certJSum cJSumTrips
  have h1 : ∀ j j' : Fin 1780,
      (∑ v ∈ (0 :: (certSig j).dedup).toFinset, ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
        certCs j * certCs j' * certJKappaN j v * certJKappaN j' v' *
          (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℤ) * (certJPsiN j v j' v' : ℤ))
      = cJSumU (cTrip j) (cTrip j') := by
    intro j j'
    rw [sum_toFinset_sig j (fun v => ∑ v' ∈ (0 :: (certSig j').dedup).toFinset,
        certCs j * certCs j' * certJKappaN j v * certJKappaN j' v' *
          (Ssum (certJBeta j v) (certJBeta j' v') 49 : ℤ) * (certJPsiN j v j' v' : ℤ))]
    unfold cJSumU cJSumV
    refine congrArg List.sum (List.map_congr_left (fun v _ => ?_))
    rw [sum_toFinset_sig j' _]
    exact congrArg List.sum (List.map_congr_left (fun v' _ => term_eq_Gtu j v j' v'))
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => h1 j j'))]
  rw [sum_ofFn_ofFn]
  rw [ofFn_pair cTrip (fun u u' => cJSumU u u')]
  rw [ofFn_cTrip]

/-- **Step 1**: the `J`-form as a double sum over the flat list `cJTrips`. -/
theorem certJSum_flat :
    certJSum = ((cJTrips.map (fun w => (cJTrips.map (fun w' => Gt w w')).sum)).sum) := by
  rw [certJSum_double, cJSumTrips]
  simp only [cJSumU_eq]
  rw [cJTrips_eq_flatMap, sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left (fun u _ => ?_))
  rw [list_sum_comm cTrips (cJFlat u) (fun u' w => ((cJFlat u').map (fun w' => Gt w w')).sum)]
  refine congrArg List.sum (List.map_congr_left (fun w _ => ?_))
  exact (sum_flatMap_map cTrips cJFlat (fun w' => Gt w w')).symm

end Commons.NumberTheory.MaynardSieve
