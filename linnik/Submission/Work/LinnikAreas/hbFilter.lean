import Mathlib

namespace Work.LinnikAreas

theorem hbFilter (N a e : ℕ) (he : 0 < e) :
    Finset.filter (fun d => d * e ≤ N) (Finset.Icc a N) = Finset.Icc a (N / e) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨ha, _⟩, hde⟩
    exact ⟨ha, (Nat.le_div_iff_mul_le he).mpr hde⟩
  · rintro ⟨ha, hd⟩
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le he).mp hd
    exact ⟨⟨ha, le_trans (Nat.le_mul_of_pos_right d he) hde⟩, hde⟩

end Work.LinnikAreas
