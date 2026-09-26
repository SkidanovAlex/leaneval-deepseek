import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.CzAux.mulV_ediv

namespace Work.SG.CzAux

/-!
# Divisibility of the cocycle `(1 - e_i) σ` for every element of the point group

The BFS table `RC` lists the elements of the class-`j` point group as
`eM j 0 = 1`, `eM j (i+1) = gMt j (par1 j i) * eM j (par2 j i)` with `par2 j i ≤ i`.
The divisibility predicate `n ∣ σ - A σ` is closed under products — indeed
`σ - (A * B) σ = (σ - A σ) + A (σ - B σ)` — so it propagates from the generators to
every listed element by strong induction on the index.
-/

open Work.SG

namespace dvdEMAux

/-- Coordinate extensionality for `Data.V3`. -/
theorem V3_ext {a b : Data.V3} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

theorem mulV_one (v : Data.V3) : Data.M3.mulV Data.M3.one v = v := by
  cases v; simp [Data.M3.mulV, Data.M3.one]

theorem mulV_mul (A B : Data.M3) (v : Data.V3) :
    Data.M3.mulV (Data.M3.mul A B) v = Data.M3.mulV A (Data.M3.mulV B v) := by
  refine V3_ext ?_ ?_ ?_ <;>
    simp only [Data.M3.mulV, Data.M3.mul] <;> ring

theorem mulV_sub (A : Data.M3) (u v : Data.V3) :
    Data.M3.mulV A (Data.V3.sub u v) = Data.V3.sub (Data.M3.mulV A u) (Data.M3.mulV A v) := by
  refine V3_ext ?_ ?_ ?_ <;>
    simp only [Data.M3.mulV, Data.V3.sub] <;> ring

/-- The multiplicative cocycle identity: `(1 - A B) σ = (1 - A) σ + A (1 - B) σ`. -/
theorem sub_mulV_mul (A B : Data.M3) (v : Data.V3) :
    Data.V3.sub v (Data.M3.mulV (Data.M3.mul A B) v) =
      Data.V3.add (Data.V3.sub v (Data.M3.mulV A v))
        (Data.M3.mulV A (Data.V3.sub v (Data.M3.mulV B v))) := by
  refine V3_ext ?_ ?_ ?_ <;>
    simp only [Data.V3.sub, Data.V3.add, Data.M3.mulV, Data.M3.mul] <;> ring

theorem V3_sub_self (a : Data.V3) : Data.V3.sub a a = Data.V3.zero := by
  cases a; simp [Data.V3.sub, Data.V3.zero]

/-- Coordinate form of `Data.V3.dvd`. -/
theorem dvd_iff' (n : ℤ) (v : Data.V3) :
    v.dvd n = true ↔ n ∣ v.x ∧ n ∣ v.y ∧ n ∣ v.z := by
  simp only [Data.V3.dvd, Bool.and_eq_true, beq_iff_eq, Int.dvd_iff_emod_eq_zero]
  tauto

theorem dvd_zero' (n : ℤ) : Data.V3.dvd n Data.V3.zero = true := by
  simp [Data.V3.dvd, Data.V3.zero]

theorem dvd_add' {n : ℤ} {u v : Data.V3} (hu : u.dvd n = true) (hv : v.dvd n = true) :
    (Data.V3.add u v).dvd n = true := by
  rw [dvd_iff'] at hu hv ⊢
  obtain ⟨hx, hy, hz⟩ := hu
  obtain ⟨gx, gy, gz⟩ := hv
  simp only [Data.V3.add]
  exact ⟨Int.dvd_add hx gx, Int.dvd_add hy gy, Int.dvd_add hz gz⟩

/-- A matrix with integer entries preserves integral divisibility: `n ∣ v → n ∣ A v`. -/
theorem dvd_mulV' (A : Data.M3) {n : ℤ} {v : Data.V3} (hv : v.dvd n = true) :
    (Data.M3.mulV A v).dvd n = true := by
  rw [dvd_iff'] at hv ⊢
  obtain ⟨hx, hy, hz⟩ := hv
  simp only [Data.M3.mulV]
  exact ⟨Int.dvd_add (Int.dvd_add (dvd_mul_of_dvd_right hx A.a) (dvd_mul_of_dvd_right hy A.b))
           (dvd_mul_of_dvd_right hz A.c),
         Int.dvd_add (Int.dvd_add (dvd_mul_of_dvd_right hx A.d) (dvd_mul_of_dvd_right hy A.e))
           (dvd_mul_of_dvd_right hz A.f),
         Int.dvd_add (Int.dvd_add (dvd_mul_of_dvd_right hx A.g) (dvd_mul_of_dvd_right hy A.h))
           (dvd_mul_of_dvd_right hz A.i)⟩

end dvdEMAux

theorem dvd_eM (j : Fin 73) (σ : Work.SG.Data.V3)
    (hσ : ∀ g, g < Work.SG.RC.KK j →
      Work.SG.Data.V3.dvd ((Work.SG.RC.Ad j).n)
        (Work.SG.Data.V3.sub σ (Work.SG.Data.M3.mulV (Work.SG.RC.gMt j g) σ)) = true) :
    ∀ i, i < Work.SG.RC.N j →
      Work.SG.Data.V3.dvd ((Work.SG.RC.Ad j).n)
        (Work.SG.Data.V3.sub σ (Work.SG.Data.M3.mulV (Work.SG.RC.eM j i) σ)) = true := by
  intro i
  exact Nat.strongRecOn (motive := fun i => i < Work.SG.RC.N j →
      Work.SG.Data.V3.dvd ((Work.SG.RC.Ad j).n)
        (Work.SG.Data.V3.sub σ (Work.SG.Data.M3.mulV (Work.SG.RC.eM j i) σ)) = true)
    i (fun k ih hk => by
      rcases k with _ | k'
      · -- `eM j 0 = 1`
        have h0 : Work.SG.RC.eM j 0 = Data.M3.one := by
          simp only [Work.SG.RC.eM]
          rcases List.head?_eq_some_iff.mp (Work.SG.RC.Ad_head j) with ⟨t, ht⟩
          rw [ht]; rfl
        rw [h0, dvdEMAux.mulV_one, dvdEMAux.V3_sub_self]
        exact dvdEMAux.dvd_zero' _
      · -- `eM j (k'+1) = gMt j (par1 j k') * eM j (par2 j k')`
        have hk' : k' + 1 < (Work.SG.RC.Ad j).n := hk
        have hpar : k' < (Work.SG.RC.Ad j).par.length := by
          rw [Work.SG.RC.par_len_eq j]; omega
        have hltn : Work.SG.RC.par2 j k' < (Work.SG.RC.Ad j).n := by
          have := Work.SG.RC.par2_le j k' hpar; omega
        have hlt : Work.SG.RC.par2 j k' < k' + 1 := by
          have := Work.SG.RC.par2_le j k' hpar; omega
        have heq : Work.SG.RC.eM j (k' + 1) =
            Data.M3.mul (Work.SG.RC.gMt j (Work.SG.RC.par1 j k'))
              (Work.SG.RC.eM j (Work.SG.RC.par2 j k')) := by
          have hh := Work.SG.RC.Ad_par_rel3 j k' (show k' < (Work.SG.RC.Ad j).n - 1 by omega)
          simpa only [Work.SG.RC.eM, Work.SG.RC.gMt, Work.SG.RC.par1, Work.SG.RC.par2,
            Work.SG.RC.par] using hh
        rw [heq, dvdEMAux.sub_mulV_mul]
        apply dvdEMAux.dvd_add'
        · exact hσ (Work.SG.RC.par1 j k')
            (by simpa [Work.SG.RC.KK] using Work.SG.RC.par1_lt j k' hpar)
        · exact dvdEMAux.dvd_mulV' _ (ih (Work.SG.RC.par2 j k') hlt hltn))

end Work.SG.CzAux
