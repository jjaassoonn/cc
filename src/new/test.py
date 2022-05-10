import random
import unittest

def swap(i, j, l) :
  l[i], l[j] = l[j], l[i]
  return l

def ignore(k, l) :
  del l[k]
  return l

class Test(unittest.TestCase):
  def setUp(self) -> None:
      self.maxDiff = None
      return super().setUp()

  # def testCase1(self):
  #   for _ in range(1000):
  #     i, j, k = random.randint(0, 99), random.randint(0, 99), random.randint(0, 99)
  #     l = [random.randint(0, 100) for _ in range(100)]
  #     lc = l.copy()
  #     if max(i, j) < k:
  #       self.assertEqual(ignore(k, swap(i, j, l)), swap(i, j, ignore(k, lc)))
  
  # def testCase2(self):
  #   for _ in range(1000):
  #     i, j, k = random.randint(0, 99), random.randint(0, 99), random.randint(0, 99)
  #     l = [random.randint(0, 100) for _ in range(100)]
  #     lc = l.copy()
  #     if k < min(i, j):
  #       # self.assertEqual(len(ignore(k, swap(i, j, l))), swap(i-1, j-1, len(ignore(k, lc))))

  #       self.assertEqual(ignore(k, swap(i, j, l)), swap(i-1, j-1, ignore(k, lc)))

  def testCase3(self):
    for _ in range(10000):
      l = [random.randint(0, 100) for _ in range(102)]
      i = random.randint(0, 101)
      j = random.randint(0, 100)
      if i <= j:
        lc = l.copy()
        del l[i]
        del l[j]
        del lc[j+1]
        del lc[i]
        self.assertEqual(l, lc)


if __name__ == '__main__' :
    unittest.main()