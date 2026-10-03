import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup
import Submission.Work.ORHughesFree.Rat.Source.SplitWords
import Submission.Work.ORHughesFree.Rat.Source.A_conj_mem

namespace Work.ORHughesFree.Rat.Source.SF

open Work.ORHughesFree

variable {U : Type} [Group U]

/-! ## Auxiliary lemmas

`mem_F_of_mem_A` is the inclusion `Rat.A V ⊆ Rat.B V = Rat(V)·U` (multiplication by `1`), which
lets us read an `Rat.A`-membership `α·φu ∈ Rat.A V` as `V ∈ Rat.F α`.

`map_conj_le_iff` and `map_conj_conj` are the elementary bookkeeping lemmas about conjugating a
subgroup by `a⁻¹` versus by `a` (recall `MulAut.conj a : x ↦ a x a⁻¹`). -/

/-- `Rat.A V ⊆ Rat.B V`: an element of the image of `Rat(V)` is `x · φ 1`. -/
theorem mem_F_of_mem_A {V : Subgroup U} {x : RatU U} (hx : x ∈ Rat.A V) : V ∈ Rat.F x := by
  rw [Rat.mem_F_iff]
  obtain ⟨β, rfl⟩ := hx
  exact ⟨β, 1, by rw [RatU.ofGroup_one, mul_one]⟩

/-- `S.map (conj a⁻¹) ≤ V` iff `S ≤ V.map (conj a)`: conjugating back and forth. -/
theorem map_conj_le_iff (a : U) (S V : Subgroup U) :
    S.map (MulAut.conj a⁻¹) ≤ V ↔ S ≤ V.map (MulAut.conj a) := by
  constructor
  · intro h s hs
    rw [Subgroup.mem_map]
    refine ⟨MulAut.conj a⁻¹ s, h (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩), ?_⟩
    show (MulAut.conj a) (MulAut.conj a⁻¹ s) = s
    rw [MulAut.conj_apply, MulAut.conj_apply]; group
  · intro h t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨s, hs, hst⟩ := ht
    rw [← hst]
    have hs' : s ∈ V.map (MulAut.conj a) := h hs
    rw [Subgroup.mem_map] at hs'
    obtain ⟨w, hw, hws⟩ := hs'
    rw [← hws]
    show (MulAut.conj a⁻¹) (MulAut.conj a w) ∈ V
    have : (MulAut.conj a⁻¹) (MulAut.conj a w) = w := by
      rw [MulAut.conj_apply, MulAut.conj_apply]; group
    rw [this]; exact hw

/-- Conjugating by `a` and then by `a⁻¹` returns the subgroup. -/
theorem map_conj_conj (a : U) (V : Subgroup U) :
    (V.map (MulAut.conj a)).map ((MulAut.conj a⁻¹ : U →* U)) = V := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj a⁻¹ : U →* U).comp (MulAut.conj a : U →* U) = MonoidHom.id U := by
    ext x
    show (MulAut.conj a⁻¹) (MulAut.conj a x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]; group
  rw [h, Subgroup.map_id]

theorem F_mul {U : Type} [Group U] {y z : Work.ORHughesFree.RatU U} {Sy Sz : Subgroup U} {uy : U}
    (hy : Work.ORHughesFree.RatU.IsWord y) (hz : Work.ORHughesFree.RatU.IsWord z)
    (hSy : Work.ORHughesFree.Rat.IsLeastF y Sy)
    (hSz : Work.ORHughesFree.Rat.IsLeastF z Sz)
    (huy : y * Work.ORHughesFree.RatU.ofGroup uy ∈ Work.ORHughesFree.Rat.A Sy) :
    ∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.F (y * z) ↔
      Sy ≤ V ∧ Sz.map (MulAut.conj uy⁻¹) ≤ V := by
  intro V
  constructor
  · -- Suppose `V ∈ F (y·z)`.
    intro hV
    rw [Rat.mem_F_iff'] at hV
    obtain ⟨u, hu⟩ := hV
    -- Split `(y·z)·φu` at the word `y`.
    have hz' : RatU.IsWord (z * RatU.ofGroup u) := RatU.IsWord.mul hz (RatU.IsWord.ofGroup u)
    have hmem : V ∈ Weak.FA (y * (z * RatU.ofGroup u)) := by
      show y * (z * RatU.ofGroup u) ∈ Rat.A V
      rw [← mul_assoc]
      exact hu
    rw [Work.ORHughesFree.Rat.Source.SW.hsplit_words hy hz', Set.mem_iUnion] at hmem
    obtain ⟨x, hx1, hx2⟩ := hmem
    have hx1A : y * RatU.ofGroup x ∈ Rat.A V := hx1
    have hx2A : RatU.ofGroup x⁻¹ * (z * RatU.ofGroup u) ∈ Rat.A V := hx2
    -- `V ∈ F y`, hence `Sy ≤ V` and `y·φuy ∈ A V`.
    have hVy' : V ∈ Rat.F (y * RatU.ofGroup x) := mem_F_of_mem_A hx1A
    have hVy : V ∈ Rat.F y := by rwa [Rat.F_mul_ofGroup] at hVy'
    have hSyV : Sy ≤ V := hSy.le hVy
    have huyA : y * RatU.ofGroup uy ∈ Rat.A V := Rat.A_mono hSyV huy
    -- The right translate set of `y` at `V` is the coset `uy·V`.
    have hy0 : y ≠ 0 := RatU.isWord_ne_zero' hy
    have hcoset := Rat.T_eq_coset hy0 hVy ((Rat.mem_T_iff y V uy).mpr huyA)
    have hxT : x ∈ Rat.Orbit.T (FreeProduct.Psi y).coeff.support V :=
      (Rat.mem_T_iff y V x).mpr hx1A
    rw [hcoset] at hxT
    obtain ⟨v, hv, rfl⟩ := hxT
    -- Divide `φx⁻¹·(z·φu) ∈ A V` by `φx ∈ A V`.
    have hvA : RatU.ofGroup v ∈ Rat.A V := Weak.A_ofGroup_mem hv
    have hx2A' : RatU.ofGroup v⁻¹ * (RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u)) ∈ Rat.A V := by
      have hvv : RatU.ofGroup (uy * v)⁻¹ = RatU.ofGroup v⁻¹ * RatU.ofGroup uy⁻¹ := by
        rw [mul_inv_rev, RatU.ofGroup_mul]
      rw [hvv, mul_assoc] at hx2A
      exact hx2A
    have hc : RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u) ∈ Rat.A V := by
      have h := Rat.A_mul hvA hx2A'
      have key : RatU.ofGroup v * (RatU.ofGroup v⁻¹ * (RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u)))
          = RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u) := by
        rw [← mul_assoc (RatU.ofGroup v) (RatU.ofGroup v⁻¹)
              (RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u)),
          ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, one_mul]
      rwa [key] at h
    -- `V ∈ F (φ(uy⁻¹)·z)`, so conjugating by `uy` puts `V.map (conj uy)` in `F z`.
    have hconj := A_conj_mem (a := uy) hc
    have hq : z * RatU.ofGroup (u * uy⁻¹) ∈ Rat.A (V.map (MulAut.conj uy)) := by
      have key : RatU.ofGroup uy * (RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup u)) * RatU.ofGroup uy⁻¹
          = z * RatU.ofGroup (u * uy⁻¹) := by
        rw [← mul_assoc (RatU.ofGroup uy) (RatU.ofGroup uy⁻¹) (z * RatU.ofGroup u),
          ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, one_mul, mul_assoc,
          ← RatU.ofGroup_mul]
      rwa [key] at hconj
    have hVz : V.map (MulAut.conj uy) ∈ Rat.F z :=
      (Rat.mem_F_iff' z _).mpr ⟨u * uy⁻¹, hq⟩
    have hSzV : Sz ≤ V.map (MulAut.conj uy) := hSz.le hVz
    exact ⟨hSyV, (map_conj_le_iff uy Sz V).mpr hSzV⟩
  · -- Conversely, suppose `Sy ≤ V` and `Sz.map (conj uy⁻¹) ≤ V`.
    rintro ⟨hSyV, hSzV⟩
    have hSz_le : Sz ≤ V.map (MulAut.conj uy) := (map_conj_le_iff uy Sz V).mp hSzV
    have hVz : V.map (MulAut.conj uy) ∈ Rat.F z := Rat.F_mono hSz_le hSz.mem
    rw [Rat.mem_F_iff'] at hVz
    obtain ⟨q, hq⟩ := hVz
    -- Conjugate back: `φ(uy⁻¹)·z·φ(q·uy) ∈ A V`.
    have hconj := A_conj_mem (V := V.map (MulAut.conj uy)) (a := uy⁻¹)
      (x := z * RatU.ofGroup q) hq
    rw [map_conj_conj uy V, inv_inv] at hconj
    have hp : RatU.ofGroup uy⁻¹ * z * RatU.ofGroup (q * uy) ∈ Rat.A V := by
      have key : RatU.ofGroup uy⁻¹ * (z * RatU.ofGroup q) * RatU.ofGroup uy
          = RatU.ofGroup uy⁻¹ * z * RatU.ofGroup (q * uy) := by
        rw [← mul_assoc (RatU.ofGroup uy⁻¹) z (RatU.ofGroup q),
          mul_assoc (RatU.ofGroup uy⁻¹ * z), ← RatU.ofGroup_mul]
      rwa [key] at hconj
    -- Multiply `y·φuy ∈ A V` and `φ(uy⁻¹)·z·φ(q·uy) ∈ A V`.
    have huyA : y * RatU.ofGroup uy ∈ Rat.A V := Rat.A_mono hSyV huy
    have hfinal : y * z * RatU.ofGroup (q * uy) ∈ Rat.A V := by
      have h := Rat.A_mul huyA hp
      have key : (y * RatU.ofGroup uy) * (RatU.ofGroup uy⁻¹ * z * RatU.ofGroup (q * uy))
          = y * z * RatU.ofGroup (q * uy) := by
        rw [← mul_assoc (y * RatU.ofGroup uy) (RatU.ofGroup uy⁻¹ * z) (RatU.ofGroup (q * uy)),
          ← mul_assoc (y * RatU.ofGroup uy) (RatU.ofGroup uy⁻¹) z,
          mul_assoc y (RatU.ofGroup uy) (RatU.ofGroup uy⁻¹),
          ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one]
      rwa [key] at h
    exact (Rat.mem_F_iff' (y * z) V).mpr ⟨q * uy, hfinal⟩

end Work.ORHughesFree.Rat.Source.SF
